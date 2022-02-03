# Trabalho 3 Seguranca computacional - RSA OAEP
# Álvaro Veloso Cavalcanti Luz - 180115391
# Vitor Vasconcelos de Oliveira - 180114778

import os
import random
import hashlib as hl
import base64
from math import ceil


class KeyGenTools():
    ''' Determina metodos que serao utilizados para geracao das chaves '''

    def __init__(self):
        pass

    def keygen(self, p, q, e):
        '''Cria chave publica(e, n) e a chave privada
        (d, n)
        input:
            p, q = numeros primos grandes, inteiros
            e = exponente da chave publica, inteiro
        output:
            chave publica, chave privada
        '''
        assert self.isPrime(p, 7) and self.isPrime(q, 7)
        assert p != q
        n = p * q
        phi = (p - 1) * (q - 1)
        if e != None:
            assert self.euclid(phi, e) == 1
        else:
            while True:
                e = random.randrange(1, phi)
                if self.euclid(e, phi) == 1:
                    break
        d = self.modinv(e, phi)
        return ((e, n), (d, n))

    def euclid(self, a, b):
        '''Calcula o MDC(maioir divisor comum) de a e b usando o algoritimo euclidiano
        input:
            a, b = dois inteiros desejados
        output:
            maior divisor comum entre "a" e "b"
        '''
        while b != 0:
            a, b = b, a % b
        return a

    def extend_euclid(self, a, b):
        '''
        Usa o algoritmo euclidiano extendido para calcular os numeros x e y para os quais:

            a * x + b * y = euclid(a, b)

        input:
            a, b = dois inteiros desejados
        output:
            y, x, q = valores correspondentes, inteiros
        '''

        if b == 0:
            return 1, 0, a
        else:
            x, y, q = self.extend_euclid(b, a % b)
            return y, x - (a // b) * y, q

    def modinv(self, a, b):
        '''
        Calcula o modulo inverso

        input:
            a, b = dois inteiros desejados
        otput:    
            o modulo inverso ou None
        '''
        x, y, q = self.extend_euclid(a, b)
        if q != 1:
            return None
        else:
            return x % b

    def millerTest(self, d, n):
        '''
        Executa o teste de primalidade de Miller-Rabin
        input:
            d = numero primo d para o qual n-1 = 2*d^r
            n = inteiro que se deseja testar
        output:
            booleano indicando a primalidade de n
        '''
        a = 2 + random.randint(1, n - 4)

        x = pow(a, d, n)
        if (x == 1 or x == n - 1):
            return True
        while (d != n - 1):
            x = (x * x) % n
            d *= 2

            if (x == 1):
                return False
            if (x == n - 1):
                return True

        return False

    def isPrime(self, n, k):
        '''
        Determina se o numero n eh primo

        input:
            n = inteiro desejado
            k = numero de vezes que o numero sera testado, inteiro
        otput:    
            Booleano indicando a primalidade de n
        '''

        if (n <= 1 or n == 4):
            return False
        if (n <= 3):
            return True

        d = n - 1
        while (d % 2 == 0):
            d //= 2
        for i in range(k):
            if (self.millerTest(d, n) == False):
                return False

        return True


class CryptoTools():
    ''' 
        Determina metodos que serao utilizados no processo de encriptacao e decriptacao
    '''

    def __init__(self):
        ''' hlen = comprimento do hash, inteiro'''
        self.hlen = len(self.sha3(b''))

    def os2ip(self, x):
        '''
        Converte o bytearray desejado para inteiro

        input:  
            x = bytearray
        output: 
            inteiro correspondente nao negativo
        '''
        return int.from_bytes(x, byteorder='big')

    def i2osp(self, x, l):
        '''
        Converte um inteiro nao negativo em bytearray

        input:
            x = inteiro nao negativo
            l = comprimento desejado em bytes
        output:
            bytearray correspondente
        '''
        return x.to_bytes(l, "big")

    def sha3(self, m):
        '''
        encripta uma mensagem com sha3

        input:
            m = mensagem para ser hasheada, bytearray
        output:
            hash correspondente, bytearray
        '''
        hasher = hl.sha3_512()
        hasher.update(m)
        return hasher.digest()

    def mgf(self, z, l):
        '''
        Gera a mascara que sera utilizada na encriptacao
        input:
            z = seed, bytearray
            l = numero de bytes desejado, inteiro
        output:
            T = mascara resultante, bytearray
        '''
        assert l < (2**32)

        T = b""

        for i in range(ceil(l / self.hlen)):
            C = self.i2osp(i, 4)
            T += self.sha3(z + C)
        return T[:l]

    def bitwise_xor(self, data, mask):
        '''
        Aplica a mascara "mask" em um bytearray "data" atraves de um xor bit a bit

        input:
            data = data, bytearray
            mask = mascara, bytearray 
        output:
            T = bytearray com a mascara aplicada, bytearray
        '''
        masked = b''
        ldata = len(data)
        lmask = len(mask)
        for i in range(max(ldata, lmask)):
            if i < ldata and i < lmask:
                masked += (data[i] ^ mask[i]).to_bytes(1, byteorder='big')
            elif i < ldata:
                masked += data[i].to_bytes(1, byteorder='big')
            else:
                break
        return masked


class Encrypt(CryptoTools):
    '''Define metodos que serao utilizados para a encriptacao RSA-OAEP'''

    def oaep_encode(self, m, k, label=b''):
        '''
        Usa o algoritmo oaep para encriptar a mensagem "m"

        input:
            m = mensagem, bytearray
            k = tamanho da chave publica em bytes, inteiro
        output:
            mensagem encriptada, bytearray 
        '''
        mlen = len(m)
        lhash = self.sha3(label)
        ps = b'\x00' * (k - mlen - 2 * self.hlen - 2)
        db = lhash + ps + b'\x01' + m
        seed = os.urandom(self.hlen)
        db_mask = self.mgf(seed, k - self.hlen - 1)
        masked_db = self.bitwise_xor(db, db_mask)
        seed_mask = self.mgf(masked_db, self.hlen)
        masked_seed = self.bitwise_xor(seed, seed_mask)
        return b'\x00' + masked_seed + masked_db

    def encrypt_rsa_oaep(self, m, public_key):
        '''
        Encripta a mensagem "m" utilizando o algoritmo RSA modelo OAEP

        input:
            m = mensagem, bytearray
            public_key = chave publica, bytearray
        output:
            mensagem encriptada, bytearray
            assinatura da mensagem, bytearray
        '''
        k = ceil((public_key[1]).bit_length() / 8)

        assert len(m) <= k - self.hlen - 2

        e, n = public_key
        c = self.oaep_encode(m, k)
        c = pow(self.os2ip(c), e, n)

        return self.i2osp(c, k)


class Decrypt(CryptoTools):
    '''Define metodos que serao utilizados para a decriptacao RSA-OAEP'''

    def oaep_decode(self, c, k, label=b''):
        '''EME-OAEP decoding
        Usa o algoritmo oaep para decriptar a mensagem "c"

         input:
            c = mensagem, bytearray
            k = tamanho da chave privada em bytes, inteiro
        output:
            mensagem decriptada, bytearray
        '''
        lhash = self.sha3(label)
        _, masked_seed, masked_db = c[:1], c[1:1 +
                                             self.hlen], c[1 + self.hlen:]
        seed_mask = self.mgf(masked_db, self.hlen)
        seed = self.bitwise_xor(masked_seed, seed_mask)
        db_mask = self.mgf(seed, k - self.hlen - 1)
        db = self.bitwise_xor(masked_db, db_mask)
        _lhash = db[:self.hlen]
        assert lhash == _lhash
        i = self.hlen
        while i < len(db):
            if db[i] == 0:
                i += 1
                continue
            elif db[i] == 1:
                i += 1
                break
            else:
                raise Exception()
        m = db[i:]
        return m

    def decrypt_rsa_oaep(self, c, private_key):
        '''Decrypt a cipher byte array with OAEP padding
        Decripta a mensagem "c" utilizando o algoritmo RSA modelo OAEP

        input:
            c = mensagem, bytearray
            private_key = chave privada, bytearray
        output:
            mensagem decriptada, bytearray
        '''
        k = ceil((private_key[1]).bit_length() / 8)
        assert len(c) == k
        assert k >= 2 * self.hlen + 2

        d, n = private_key
        m = pow(self.os2ip(c), d, n)
        m = self.i2osp(m, k)

        return self.oaep_decode(m, k)


class Receiver(KeyGenTools, Decrypt):
    '''
    Responsavel por receber a mensagem encripitada, decripita-la e testa-la com a Assinatura
    '''

    def __init__(self, newKey=True):
        '''construtor da classe Receiver
        input:
            newKey = indica se uma nova chave sera gerada, booleano
        '''
        e = 0x010001

        if newKey:
            print("Gerando chaves(0/2)...")
            p = 1
            while (not self.isPrime(p, 7)):
                p = random.randint(2**1023, 2**1024)
            print("Gerando chaves(1/2)...")
            q = 1
            while (not self.isPrime(q, 7)) or p == q:
                q = random.randint(2**1023, 2**1024)
            print("Gerando chaves(2/2)...")
            print("Geracao completa!")
            # salvar nova chave
            print("Selecione um nome para o novo arquivo de chaves:\n")
            print(
                "Aviso: nao usar caracteres especiais ou especificar a extensao do arquivo")
            print("Exemplo de entrada: >exemplo\n")
            name = str(input(">"))
            self.name = name
            with open(name + ".txt", "w+") as f:
                f.write(str(p) + "\n")
                f.write(str(q) + "\n")
        else:
            # usar chave antiga
            print("Digite o arquivo de chave que deseja utilizar\n")
            print(
                "Aviso: nao usar caracteres especiais ou especificar a extensao do arquivo")
            print("Exemplo de entrada: >exemplo\n")
            name = str(input(">"))
            self.name = name
            with open(name + ".txt", "r") as f:
                if f:
                    p = int(f.readline())
                    q = int(f.readline())
        print("----------------Primos em hexadecimal----------------------")
        print("primo 1:", hex(p))
        print("primo 2:", hex(q))
        KeyGenTools.__init__(self)
        Decrypt.__init__(self)
        self.pubkey, self.privkey = self.keygen(p, q, e)
        print("---------------Chaves de criptacao --------------")
        print("Chave publica:", self.pubkey)
        print("Chave privada:\n\n", self.privkey[0])

    def start_connection(self):
        '''inicia a conexao entre sender e receiver instanciando o server'''
        self.server = [Server(self.pubkey, self.name)]
        return self.server

    def decrypt_message(self):
        '''decripta a mensagem armazenada no server'''
        signature, message = self.server[0].get_message()
        d, n = self.server[0].pubkeySender
        decrypted_message = self.decrypt_rsa_oaep(
            message, self.privkey)

        # print(signature)

        s = self.i2osp(pow(self.os2ip(signature), d, n), 64)

        if(s == self.sha3(decrypted_message)):
            print("Mensagem recebida com sucesso!!")
            print("Mensagem decriptada:", decrypted_message.decode("utf-8"), "\n")
            print("---------------------------------------------")
        else:
            print("ERRO: Assinatura da mensagem incompativel.")


class Server():
    '''
    Determina a comunicacao entre Sender e Receiver, garantindo acesso apenas a mensagem encriptada e a chave publica de ambos
    '''

    def __init__(self, pubkeyReceiver, name):
        '''construtor da classe server'''
        self.pubkeyReceiver = pubkeyReceiver
        self.name = name

    def set_message(self, signature, cryptedMessage):
        '''grava a mensagem e a assinatura no .txt correspondente
        input: 
            signature, cryptedMessage = bytearrays
        '''
        self.cryptedMessage = cryptedMessage
        # print(signature)
        base64EncodedStr = base64.b64encode(cryptedMessage)
        base64EncodedStrS = base64.b64encode(signature)
        with open('mensagem' + self.name + '.txt', 'w+') as f:
            print("Assinatura da mensagem:", base64EncodedStrS.decode('utf-8'))
            print("Mensagem encriptada: " +
                  base64EncodedStr.decode('utf-8')+"\n")
            f.write(base64EncodedStrS.decode('utf-8')+"\n")
            f.write(base64EncodedStr.decode('utf-8'))

    def get_message(self):
        '''le a mensagem gravada no txt correspondente
        output:
            signature, message = assinatura e mensagem encriptada, bytearray
        '''
        with open('mensagem'+self.name+'.txt', 'r') as f:
            if not f:
                print('ERRO: Arquivo de mensagem inexistente')
                return None
            else:
                m = f.readline()
                signature = base64.b64decode(m.encode("utf-8"))
                m = f.readline()
                message = base64.b64decode(m.encode("utf-8"))
                return signature, message

    # sets e gets para valores especificos
    def set_pubkeySender(self, pubkeySender): self.pubkeySender = pubkeySender
    def get_e(self): return self.e
    def get_n(self): return self.n


class Sender(Encrypt, KeyGenTools):
    '''
    Responsavel por encripitar a mensagem e a assinatura e envia-las ao sever
    '''

    def __init__(self, server):
        '''construtor da classe sender
        input:
            server = ponteiro para acessar o Server instanciado pela classe Receiver, lista com um objeto server instanciado, [Server]
        '''
        self.server = server
        '''p e q sao primos grandes constantes que criarao a chave privada e publica do server para ser utilizada na assinatura'''
        e = 0x010001
        p = 97962796904280205888084811562964488190962410580438986602772964729043975540681631621472675024214515491932452297662896068200477857556195577301442157032294788012249197257876876439702478794510158895189770668271842399008851096255918615617091562859396319516675952918545998915860198564813082383638996319228274522199
        q = 179254215470244753801670806037636828877229308262366906189173021362198522014648917380717440609954562680936353318826278100387818010717325117950339338189158413352932790197268235586554618256304106325838871838101470934772890880184013442978003681873677779889327057473152412199836756580050573796447220026994889221457
        super().__init__()
        self.pubkey, self.privkey = self.keygen(p, q, e)
        self.server[0].set_pubkeySender(self.pubkey)

    def cript_message(self, message):
        '''encripta a mensagem desejada
        input:
            message = mensagem desejada, string
        '''
        signature = self.create_signature(message)
        cryptedMessage = self.encrypt_rsa_oaep(
            message.encode('utf-8'), self.server[0].pubkeyReceiver)
        # print((cryptedMessage))
        self.server[0].set_message(signature, cryptedMessage)

    def create_signature(self, message):
        '''gera a assinatura da mensagem
        input:
            message = mensagem desejada, string
        output: 
            s = assinatura da mensagem, bytearray 
        '''
        e, n = self.privkey
        s = self.i2osp(
            pow(self.os2ip(self.sha3(message.encode("utf-8"))), e, n), 256)

        return s


def clearConsole():
    '''
    Funcao que limpa o terminal
    '''
    command = 'clear'
    if os.name in ('nt', 'dos'):  # If Machine is running on Windows, use cls
        command = 'cls'
    os.system(command)


def main():
    mainInterface = "Bem-vindo ao encriptador e decriptador de RSA-OAEP!\n\n"
    mainInterface += "\tEste programa implementa um algoritmo RSA tipo OAEP e replica como seria uma aplicacao deste algoritmo na comunicacao em um servidor utilizando orientacao a objetos\n\n"
    mainInterface += "Selecione uma das opcoes:\n"
    mainInterface += "\t1 - Encriptar uma mensagem\n"
    mainInterface += "\t2 - Decriptar uma mensagem\n"
    mainInterface += "\tS - Sair\n\n"
    mainOpt = None
    while not (mainOpt == 's' or mainOpt == 'S'):
        mainOpt = str(input(mainInterface + ">"))
        if mainOpt == '1':
            clearConsole()
            print("Deseja utilizar uma chave de sessao ja definida anteriormente?(y/n)")
            if(str(input(">")) == "n"):
                receiver = Receiver(newKey=True)
            else:
                avisoInterface = "Aviso: a mensagem encriptada em com essa chave anteriormente sera sobrescrita, desejas continuar? (y/n) "
                if(str(input(avisoInterface + ">")) != "y"):
                    continue
                clearConsole()
                receiver = Receiver(newKey=False)
            print("Conexao entre sender e receiver criada")
            sender = Sender(receiver.start_connection())

            cryptInterface = "Defina qual mensagem deve ser encriptada:\n"
            sender.cript_message(str(input(cryptInterface + ">")))
        elif mainOpt == '2':
            try:
                receiver = Receiver(newKey=False)
            except:
                clearConsole()
                print('ERRO: Arquivo de chave inexistente\n')
                continue
            sender = Sender(receiver.start_connection())
            try:
                receiver.decrypt_message()
            except AssertionError:
                print("ERRO: chave incompativel")
            except FileNotFoundError:
                print("ERRO: arquivo de mensagem inexistente")
        elif not (mainOpt == 's' or mainOpt == 'S'):
            clearConsole()
            print("ERRO: Opcao inexistente\n\n")


if __name__ == "__main__":
    main()
