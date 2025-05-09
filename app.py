import base64
import uuid
import requests
import multiprocessing
import os
import json
import secrets
import hashlib
import time
from functools import wraps
from datetime import datetime
from flask import Flask, request, jsonify, render_template, session, url_for, redirect, send_from_directory
from ecdsa import SigningKey, SECP256k1, VerifyingKey, BadSignatureError
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.backends import default_backend

#==========BLOCKCHAIN==============
class Transaccion:
    def __init__(self, mensaje, firma_b64, clave_publica_b64):
        self.mensaje = mensaje
        self.firma = firma_b64
        self.clave_publica = clave_publica_b64

    def verificar_firma(self):
        try:
            firma_bytes = base64.b64decode(self.firma)
            clave_bytes = base64.b64decode(self.clave_publica)
            public_key = VerifyingKey.from_string(clave_bytes, curve=SECP256k1)
            public_key.verify(firma_bytes, self.mensaje.encode())
            return True
        except (BadSignatureError, ValueError, Exception) as e:
            print(f"Error de verificación de firma: {e}")
            return False

    def to_dict(self):
        return {
            "mensaje": self.mensaje,
            "firma": self.firma,
            "clave_publica": self.clave_publica
        }

class Bloque:
    def __init__(self, indice, timestamp, transacciones, prev_hash):
        self.indice = indice
        self.timestamp = timestamp
        self.transacciones = transacciones  # lista de objetos Transaccion
        self.prev_hash = prev_hash
        self.hash = self.calcular_hash()

    @staticmethod
    def from_dict(data):
        transacciones = [
            Transaccion(tx["mensaje"], tx["firma"], tx["clave_publica"])
            for tx in data["transacciones"]
        ]
        bloque = Bloque(
            data["indice"],
            data["timestamp"],
            transacciones,
            data["prev_hash"]
        )
        bloque.hash = data["hash"]
        return bloque

    def calcular_hash(self):
        datos_bloque = {
            "indice": self.indice,
            "timestamp": self.timestamp,
            "transacciones": [tx.to_dict() for tx in self.transacciones],
            "prev_hash": self.prev_hash
        }
        bloque_string = json.dumps(datos_bloque, sort_keys=True).encode()
        return hashlib.sha256(bloque_string).hexdigest()

    def to_dict(self):
        return {
            "indice": self.indice,
            "timestamp": self.timestamp,
            "fecha_legible": datetime.fromtimestamp(self.timestamp).strftime('%Y-%m-%d %H:%M:%S'),
            "transacciones": [tx.to_dict() for tx in self.transacciones],
            "prev_hash": self.prev_hash,
            "hash": self.hash
        }

class Blockchain:
    def __init__(self):
        self.cargar_cadena()

    def guardar_cadena(self, filename='blockchain.json'):
        with open(filename, 'w') as f:
            json.dump([bloque.to_dict() for bloque in self.chain], f, indent=4)

    def cargar_cadena(self, filename='blockchain.json'):
        if os.path.exists(filename):
            with open(filename, 'r') as f:
                data = json.load(f)
                self.chain = [Bloque.from_dict(b) for b in data]
                print("Cadena cargada desde archivo.")
        else:
            print("No se encontró archivo. Se crea bloque génesis.")
            self.chain = [self.crear_bloque_genesis()]

    def crear_bloque_genesis(self):
        return Bloque(0, time.time(), [], "0")

    def obtener_ultimo_bloque(self):
        return self.chain[-1]

    def agregar_bloque(self, transacciones):
        # Verificar todas las firmas antes de añadir el bloque
        for tx in transacciones:
            if not tx.verificar_firma():
                print("Transacción inválida detectada. Bloque no añadido.")
                return None

        bloque_nuevo = Bloque(
            indice=len(self.chain),
            timestamp=time.time(),
            transacciones=transacciones,
            prev_hash=self.obtener_ultimo_bloque().hash
        )
        self.chain.append(bloque_nuevo)
        self.guardar_cadena()
        print(f"Bloque {bloque_nuevo.indice} añadido con éxito.")
        return bloque_nuevo

    def agregar_bloque_objeto(self, bloque):
        # Verificar validez de transacciones
        for tx in bloque.transacciones:
            if not tx.verificar_firma():
                print("Transacción inválida detectada. Bloque no añadido.")
                return None

        # Verificar integridad del hash
        if bloque.hash != bloque.calcular_hash():
            print("Hash del bloque inválido. Bloque no añadido.")
            return None

        # Verificar consistencia con la cadena
        if bloque.prev_hash != self.obtener_ultimo_bloque().hash:
            print("El hash del bloque anterior no coincide. Bloque no añadido.")
            return None

        self.chain.append(bloque)
        self.guardar_cadena()
        print(f"Bloque {bloque.indice} añadido con éxito.")
        return bloque

    @staticmethod
    def es_valida_cadena(cadena):
        for i in range(1, len(cadena)):
            bloque_actual = cadena[i]
            bloque_anterior = cadena[i - 1]

            if bloque_actual.hash != bloque_actual.calcular_hash():
                print(f"Hash inválido en el bloque {i}.")
                return False
            if bloque_actual.prev_hash != bloque_anterior.hash:
                print(f"El hash anterior del bloque {i} no coincide.")
                return False

            for tx in bloque_actual.transacciones:
                if not tx.verificar_firma():
                    print(f"Firma inválida en el bloque {i}.")
                    return False
        return True
#==================================
def iniciar_nodo(puerto, vecinos, password):
    app = Flask(__name__, static_folder="static", template_folder="templates")
    app.secret_key = os.urandom(24)
    blockchain = Blockchain()
    nodos_vecinos = set(vecinos)
    COMENTARIOS_PATH = "comentarios.json"

    # VARIABLES GLOBALES (inicializadas en None)
    private_key_b64, public_key_b64, node_id, private_key = None, None, None, None
    path_claves = f"claves_{puerto}.json"

    node_id = str(uuid.uuid4()).replace("-", "")
    print(f"\n🟢 Nodo {puerto} iniciado con ID: {node_id}")
    print(f" * Accede a: http://127.0.0.1:{puerto}")

    def descifrar_clave_privada(clave_cifrada_b64, password):
        try:
            data = base64.b64decode(clave_cifrada_b64)
            salt, iv, encrypted = data[:16], data[16:32], data[32:]
            kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000,
                             backend=default_backend())
            key = kdf.derive(password.encode())
            cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
            decryptor = cipher.decryptor()
            resultado = decryptor.update(encrypted) + decryptor.finalize()

            if not resultado.startswith(b"CLAVE:"):
                raise ValueError("❌ Descifrado inválido: prefijo no encontrado")
            clave_real = resultado[len(b"CLAVE:"):]

            if len(clave_real) != 32:
                raise ValueError("❌ Descifrado inválido: longitud inesperada")

            return clave_real
        except Exception as e:
            print(f"❌ Descifrado fallido: {e}")
            raise

    if os.path.exists(path_claves):
        try:
            with open(path_claves, "r") as f:
                nodo_data = json.load(f)
                public_key_b64 = nodo_data["clave_publica"]
                node_id = nodo_data["node_id"]
                clave_privada_cifrada = nodo_data["clave_privada_cifrada"]

                # Descifrar la clave privada
                private_key_bytes = descifrar_clave_privada(clave_privada_cifrada, password)
                private_key = SigningKey.from_string(private_key_bytes, curve=SECP256k1)

                # Verificar que las claves coincidan
                public_key_local = private_key.get_verifying_key()
                if base64.b64encode(public_key_local.to_string()).decode() != public_key_b64:
                    raise ValueError("Las claves pública y privada no coinciden")

                print(f"✅ Credenciales cargadas para el nodo {puerto}")
        except Exception as e:
            print(f"❌ Error al cargar credenciales: {e}")
            # Eliminar el archivo corrupto/inválido
            if os.path.exists(path_claves):
                os.remove(path_claves)

    def require_login(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            if not session.get("logueado"):
                return redirect("/auth")
            return f(*args, **kwargs)

        return decorated_function

    def cargar_o_generar_claves_y_id(path="claves.json"):
        with open(path, "r") as f:
            data = json.load(f)
            clave_privada_cifrada = data["clave_privada"]
            clave_privada_bytes = descifrar_clave_privada(clave_privada_cifrada, password)
            private_key = SigningKey.from_string(clave_privada_bytes, curve=SECP256k1)
            return data["clave_privada"], data["clave_publica"], data["node_id"], private_key

    # Intentar cargar claves si existen (por ejemplo tras reinicio y login previo)
    if password and os.path.exists(path_claves):
        try:
            clave_privada_cifrada, public_key_b64, node_id, private_key = cargar_o_generar_claves_y_id(path_claves)
            private_key_b64 = clave_privada_cifrada
        except Exception as e:
            print(f"❌ Error al cargar claves iniciales: {e}")

    def cifrar_mensaje_aes(mensaje, password):
        salt = os.urandom(16)
        kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000, backend=default_backend())
        key = kdf.derive(password.encode())
        iv = secrets.token_bytes(16)
        cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
        encryptor = cipher.encryptor()
        cifrado = encryptor.update(mensaje.encode()) + encryptor.finalize()
        return base64.b64encode(salt + iv + cifrado).decode()

    def descifrar_mensaje_aes(cifrado_b64, password):
        data = base64.b64decode(cifrado_b64)
        salt, iv, cifrado = data[:16], data[16:32], data[32:]
        kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000, backend=default_backend())
        key = kdf.derive(password.encode())
        cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
        decryptor = cipher.decryptor()
        mensaje = decryptor.update(cifrado) + decryptor.finalize()
        return mensaje.decode()

    @app.route("/")
    @require_login
    def index():
        return render_template("index.html")

    @require_login
    @app.route("/claves", methods=["GET"])
    def obtener_claves():
        clave_privada_visible = None
        if private_key:
            clave_privada_visible = base64.b64encode(private_key.to_string()).decode()
        return jsonify({
            "clave_privada": clave_privada_visible,
            "clave_publica": public_key_b64,
            "nodo_id": node_id
        })

    @require_login
    @app.route("/firmar", methods=["POST"])
    def firmar_mensaje_endpoint():
        data = request.json
        mensaje = data.get("mensaje")
        cifrar = data.get("cifrar", False)
        password = data.get("password", "")

        if not mensaje:
            return jsonify({"error": "Mensaje requerido"}), 400

        if cifrar and password:
            mensaje = cifrar_mensaje_aes(mensaje, password)

        firma = private_key.sign(mensaje.encode())
        firma_b64 = base64.b64encode(firma).decode()

        return jsonify({
            "mensaje": mensaje,
            "firma": firma_b64
        })

    @require_login
    @app.route("/descifrar", methods=["POST"])
    def descifrar_mensaje_endpoint():
        data = request.json
        mensaje_cifrado = data.get("mensaje")
        password = data.get("password", "")
        try:
            claro = descifrar_mensaje_aes(mensaje_cifrado, password)
            return jsonify({"mensaje_descifrado": claro})
        except Exception:
            return jsonify({"error": "No se pudo descifrar. ¿Contraseña incorrecta?"}), 400

    @require_login
    @app.route("/transaccion", methods=["POST"])
    def agregar_transaccion():
        data = request.json
        mensaje = data.get("mensaje")
        firma = data.get("firma")
        clave_publica = data.get("clave_publica")

        if not all([mensaje, firma, clave_publica]):
            return jsonify({"error": "Datos incompletos"}), 400

        tx = Transaccion(mensaje, firma, clave_publica)
        if not tx.verificar_firma():
            return jsonify({"error": "Firma inválida"}), 400

        nuevo_bloque = blockchain.agregar_bloque([tx])
        if nuevo_bloque is None:
            return jsonify({"error": "Error al añadir el bloque"}), 400

        for nodo in nodos_vecinos:
            try:
                requests.post(f"{nodo}/recibir_bloque", json=nuevo_bloque.to_dict(), timeout=3)
                # Sincronización después de enviar el bloque
                requests.get(f"{nodo}/sincronizar", timeout=3)
            except requests.exceptions.RequestException as e:
                print(f"❌ Error al propagar a {nodo}: {e}")

        return jsonify({
            "mensaje": "Transacción agregada",
            "bloque": nuevo_bloque.to_dict()
        })

    @app.route("/recibir_bloque", methods=["POST"])
    def recibir_bloque():
        data = request.get_json()
        if not isinstance(data, dict):
            return jsonify({"error": "Bloque no recibido"}), 400

        transacciones = [
            Transaccion(tx["mensaje"], tx["firma"], tx["clave_publica"])
            for tx in data.get("transacciones", [])
        ]

        if any(b.hash == data["hash"] for b in blockchain.chain):
            return jsonify({"mensaje": "Bloque duplicado ignorado"}), 200

        ultimo_bloque = blockchain.obtener_ultimo_bloque()
        if data["prev_hash"] != ultimo_bloque.hash:
            print("⛔ Hash anterior no coincide. Considera sincronizar.")
            return jsonify({"error": "Prev_hash inválido"}), 400

        nuevo_bloque = Bloque.from_dict(data)
        cadena_temporal = blockchain.chain + [nuevo_bloque]

        if Blockchain.es_valida_cadena(cadena_temporal):
            blockchain.chain.append(nuevo_bloque)

            # Intentar sincronizar con vecinos tras recibir bloque válido
            for nodo in nodos_vecinos:
                try:
                    requests.get(f"{nodo}/sincronizar", timeout=3)
                except requests.exceptions.RequestException:
                    pass

            return jsonify({"mensaje": "Bloque recibido y añadido"}), 200
        else:
            return jsonify({"error": "Bloque inválido"}), 400

    @app.route("/registrar_nodo", methods=["POST"])
    def registrar_nodo():
        data = request.get_json()
        if not isinstance(data, dict):
            return jsonify({"error": "Datos mal formateados"}), 400

        direccion = data.get("direccion")
        if direccion:
            nodos_vecinos.add(direccion)
            for nodo in nodos_vecinos:
                if nodo != direccion:
                    try:
                        requests.post(f"{nodo}/registrar_nodo", json={"direccion": direccion}, timeout=3)
                    except requests.exceptions.RequestException as e:
                        print(f"❌ Error al propagar registro de nodo a {nodo}: {e}")

            try:
                requests.get(f"{direccion}/sincronizar", timeout=5)
            except requests.exceptions.RequestException as e:
                print(f"⚠️ No se pudo sincronizar con el nodo {direccion}: {e}")

            return jsonify({"mensaje": f"Nodo {direccion} registrado"}), 200
        return jsonify({"error": "Dirección requerida"}), 400

    @app.route("/sincronizar", methods=["GET"])
    def sincronizar_cadena():
        cadena_mas_larga = blockchain.chain
        for nodo in nodos_vecinos:
            try:
                res = requests.get(f"{nodo}/chain", timeout=4)
                if res.status_code == 200:
                    datos = res.json()
                    cadena_externa = datos.get("cadena", [])
                    if len(cadena_externa) > len(cadena_mas_larga):
                        from_dict_chain = [Bloque.from_dict(b) for b in cadena_externa]
                        if Blockchain.es_valida_cadena(from_dict_chain):
                            blockchain.chain = from_dict_chain
                            print(f"✅ Cadena sincronizada con nodo: {nodo}")
                        else:
                            print(f"⚠️ La cadena externa de {nodo} no es válida. No se sincroniza.")
                    else:
                        print(f"⚠️ La cadena externa de {nodo} es más corta. No se sincroniza.")
            except requests.exceptions.RequestException as e:
                print(f"⚠️ Error al conectar con {nodo}: {e}")
        return jsonify({"mensaje": "Sincronización completada", "longitud": len(blockchain.chain)})

    @app.route("/chain", methods=["GET"])
    def obtener_cadena():
        cadena_serializada = [bloque.to_dict() for bloque in blockchain.chain]
        return jsonify({"longitud": len(cadena_serializada), "cadena": cadena_serializada})

    @require_login
    @app.route("/validar", methods=["GET"])
    def validar_cadena():
        return jsonify({"valida": Blockchain.es_valida_cadena(blockchain.chain)})

    @require_login
    @app.route("/nodos", methods=["GET"])
    def obtener_nodos():
        return jsonify({"nodos_vecinos": list(nodos_vecinos)})

    def cargar_comentarios():
        """Carga los comentarios desde el archivo, o devuelve una lista vacía si no existe."""
        if not os.path.exists(COMENTARIOS_PATH):
            return []
        with open(COMENTARIOS_PATH, "r", encoding="utf-8") as f:
            return json.load(f)

    def guardar_comentarios(data):
        """Guarda la lista de comentarios en disco."""
        with open(COMENTARIOS_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    @require_login
    @app.route("/comentarios", methods=["GET"])
    def obtener_comentarios():
        """Devuelve la lista de comentarios guardados."""
        comentarios = cargar_comentarios()
        return jsonify(comentarios)

    @require_login
    @app.route("/comentarios", methods=["POST"])
    def agregar_comentario():
        data = request.get_json()
        nuevo = {
            "id": str(uuid.uuid4()),
            "texto": data.get("texto", ""),
            "fecha": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "autor": node_id
        }
        comentarios = cargar_comentarios()
        comentarios.append(nuevo)
        guardar_comentarios(comentarios)

        #  Propagar a vecinos
        for nodo in nodos_vecinos:
            try:
                requests.post(f"{nodo}/comentarios/propagar", json=nuevo, timeout=3)
            except requests.exceptions.RequestException as e:
                print(f"⚠️ No se pudo propagar comentario a {nodo}: {e}")

        return jsonify({"status": "ok", "comentario": nuevo})

    @app.route("/comentarios/propagar", methods=["POST"])
    def recibir_comentario_propagado():
        data = request.get_json()
        comentarios = cargar_comentarios()
        data.setdefault("autor", node_id)
        comentarios.append(data)
        guardar_comentarios(comentarios)
        return jsonify({"status": "ok"}), 200

    def sincronizar_comentarios():
        comentarios_actuales = cargar_comentarios()
        comentarios_por_id = {c["id"]: c for c in comentarios_actuales}

        for nodo in nodos_vecinos:
            try:
                res = requests.get(f"{nodo}/comentarios", timeout=3)
                if res.status_code == 200:
                    comentarios_vecino = res.json()
                    for comentario in comentarios_vecino:
                        if comentario["id"] not in comentarios_por_id:
                            comentarios_por_id[comentario["id"]] = comentario
            except requests.exceptions.RequestException as e:
                print(f"⚠️ No se pudo sincronizar comentarios desde {nodo}: {e}")

        comentarios_combinados = list(comentarios_por_id.values())
        guardar_comentarios(comentarios_combinados)
        print(f"✅ Comentarios sincronizados con {len(nodos_vecinos)} nodos.")

    def clave_publica_ya_existe(nueva_pub_bytes):
        carpeta = "usuarios"
        if not os.path.exists(carpeta):
            return False
        for archivo in os.listdir(carpeta):
            if archivo.endswith(".pub"):
                with open(os.path.join(carpeta, archivo), "r") as f:
                    contenido = f.read().replace("-----BEGIN PUBLIC KEY-----", "").replace("-----END PUBLIC KEY-----",
                                                                                           "").strip()
                    try:
                        existente_bytes = base64.b64decode(contenido)
                        if existente_bytes == nueva_pub_bytes:
                            return True
                    except Exception:
                        continue
        return False

    @app.route("/auth", methods=["GET", "POST"])
    def auth():
        nonlocal private_key, public_key_b64, node_id, private_key_b64

        if request.method == "GET":
            return render_template("auth.html")

        accion = request.form.get("accion")
        password = request.form.get("password", "").strip()

        if not password:
            return render_template("auth.html", login_error="❌ Contraseña requerida")

        if accion == "login":
            archivo = request.files.get("clave_enc")
            if not archivo:
                return render_template("auth.html", login_error="❌ Archivo de clave requerido")

            path_claves = f"claves_{puerto}.json"
            if not os.path.exists(path_claves):
                return render_template("auth.html", login_error="❌ No hay usuario registrado en este nodo")

            try:
                # 1. Leer archivo de claves del nodo
                with open(path_claves, "r") as f:
                    nodo_data = json.load(f)
                    clave_publica_registrada = nodo_data["clave_publica"]
                    clave_privada_cifrada = nodo_data["clave_privada_cifrada"]

                # 2. Descifrar la clave privada almacenada (para verificar contraseña)
                private_key_bytes = descifrar_clave_privada(clave_privada_cifrada, password)

                # 3. Leer y verificar el archivo subido
                archivo_data = archivo.read()
                salt, iv, encrypted = archivo_data[:16], archivo_data[16:32], archivo_data[32:]

                # 4. Descifrar el archivo subido
                kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt,
                                 iterations=100_000, backend=default_backend())
                key = kdf.derive(password.encode())
                cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
                decrypted = cipher.decryptor().update(encrypted) + cipher.decryptor().finalize()

                if not decrypted.startswith(b"CLAVE:"):
                    return render_template("auth.html", login_error="❌ Formato de clave inválido")

                # 5. Obtener clave pública del archivo subido
                clave_privada_subida = decrypted[len(b"CLAVE:"):]
                private_key_temp = SigningKey.from_string(clave_privada_subida, curve=SECP256k1)
                public_key_temp = private_key_temp.get_verifying_key()
                public_key_b64_subida = base64.b64encode(public_key_temp.to_string()).decode()

                # 6. Verificar coincidencia con clave pública registrada
                if public_key_b64_subida != clave_publica_registrada:
                    return render_template("auth.html",
                                           login_error="❌ Las credenciales no coinciden con este nodo")

                # 7. Si todo está bien, establecer las variables de sesión
                private_key = private_key_temp
                public_key_b64 = public_key_b64_subida
                session["logueado"] = True
                session["node_id"] = node_id
                print(f"✅ Login exitoso para nodo {puerto}")
                return redirect(url_for("index"))

            except Exception as e:
                print(f"❌ Error durante login: {str(e)}")
                return render_template("auth.html",
                                       login_error=f"❌ Error de autenticación: {str(e)}")

        # === REGISTRO DE NUEVO USUARIO ===
        if accion == "registrar":
            if session.get("logueado"):
                return render_template("auth.html",registro_error="⚠️ Este nodo ya tiene una clave registrada. No puedes volver a registrarte.")
            # Generar claves
            private_key_local = SigningKey.generate(curve=SECP256k1)
            public_key = private_key_local.get_verifying_key()
            private_key_bytes = private_key_local.to_string()
            public_key_bytes = public_key.to_string()
            # Verificar duplicado
            if clave_publica_ya_existe(public_key_bytes):
                return render_template("auth.html", registro_error="❌ Ya existe un usuario con esta clave pública.")
            # Cifrar con contraseña
            salt = os.urandom(16)
            iv = os.urandom(16)
            kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt,
                             iterations=100_000, backend=default_backend())
            key = kdf.derive(password.encode())
            contenido = b"CLAVE:" + private_key_bytes
            cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
            encrypted = cipher.encryptor().update(contenido) + cipher.encryptor().finalize()

            # Guardar información de las claves (ESTA PARTE DEBE ESTAR DENTRO DEL BLOQUE DE REGISTRO)
            clave_data = {
                "clave_publica": base64.b64encode(public_key_bytes).decode(),
                "node_id": node_id,
                "clave_privada_cifrada": base64.b64encode(salt + iv + encrypted).decode()
            }

            with open(f"claves_{puerto}.json", "w") as f:
                json.dump(clave_data, f)
            # ID de usuario
            node_id = str(uuid.uuid4()).replace("-", "")
            os.makedirs("usuarios", exist_ok=True)
            enc_filename = f"clave_{node_id}.enc"
            pub_filename = f"clave_{node_id}.pub"

            enc_path = os.path.join("usuarios", enc_filename)
            pub_path = os.path.join("usuarios", pub_filename)

            with open(enc_path, "wb") as f:
                f.write(salt + iv + encrypted)

            with open(pub_path, "w") as f:
                pem = "-----BEGIN PUBLIC KEY-----\n" + base64.b64encode(
                    public_key_bytes).decode() + "\n-----END PUBLIC KEY-----\n"
                f.write(pem)

            # Mostrar ruta relativa para Jinja
            return render_template("auth.html", clave_enc=f"usuarios/{enc_filename}",
                                   clave_pub=f"usuarios/{pub_filename}")

        # === INICIO DE SESIÓN USANDO ARCHIVO .enc ===
        elif accion == "login":
            archivo = request.files.get("clave_enc")
            if not archivo:
                return render_template("auth.html", login_error="❌ Archivo de clave requerido")

                # Cargar las claves registradas para este nodo
            path_claves = f"claves_{puerto}.json"
            if not os.path.exists(path_claves):
                return render_template("auth.html", login_error="❌ No hay usuario registrado en este nodo")

            with open(path_claves, "r") as f:
                nodo_data = json.load(f)
                clave_publica_registrada = nodo_data["clave_publica"]

            try:
                # Proceso de descifrado (igual que antes)...
                data = archivo.read()
                salt, iv, encrypted = data[:16], data[16:32], data[32:]

                kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt,
                                 iterations=100_000, backend=default_backend())
                key = kdf.derive(password.encode())

                cipher = Cipher(algorithms.AES(key), modes.CFB(iv), backend=default_backend())
                decrypted = cipher.decryptor().update(encrypted) + cipher.decryptor().finalize()

                if not decrypted.startswith(b"CLAVE:"):
                    raise ValueError("Prefijo no válido")

                clave_privada_bytes = decrypted[len(b"CLAVE:"):]
                private_key_local = SigningKey.from_string(clave_privada_bytes, curve=SECP256k1)
                public_key_local = private_key_local.get_verifying_key()
                public_key_bytes = public_key_local.to_string()
                public_key_b64 = base64.b64encode(public_key_bytes).decode()

                # VERIFICACIÓN CRUCIAL: Comparar con la clave pública registrada
                if public_key_b64 != clave_publica_registrada:
                    return render_template("auth.html",
                                           login_error="❌ Estas credenciales no están registradas en este nodo")

                # Si todo está bien, continuar con el login
                private_key = private_key_local
                session["logueado"] = True
                return redirect(url_for("index"))

            except Exception as e:
                print(f"❌ Login fallido: {e}")
                return render_template("auth.html",
                                       login_error="❌ No se pudo descifrar la clave. ¿Contraseña correcta?")
        return "❌ Acción inválida", 400

    @app.route("/usuarios/<filename>")
    def descargar_archivo(filename):
        return send_from_directory("usuarios", filename, as_attachment=True)

    @app.route("/logout", methods=["POST"])
    @require_login
    def logout():
        """Cierra sesión y elimina las credenciales del nodo"""
        session.clear()
        path_claves = f"claves_{puerto}.json"
        if os.path.exists(path_claves):
            os.remove(path_claves)
        return redirect(url_for("auth"))

    sincronizar_comentarios()
    app.run(host="0.0.0.0", port=puerto)

# Lanzador de múltiples nodos
if __name__ == "__main__":
    puertos = [5000, 5001]
    procesos = []
    blockchain = Blockchain()
    print("Blockchain inicializada con bloque génesis.")

    password = None
    for puerto in puertos:
        vecinos = [f"http://localhost:{p}" for p in puertos if p != puerto]
        p = multiprocessing.Process(target=iniciar_nodo, args=(puerto, vecinos, password))
        p.start()
        procesos.append(p)

    print("🚀 Todos los nodos fueron lanzados automáticamente")

    for p in procesos:
        p.join()











