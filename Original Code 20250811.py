from basicblockchains_ecc import elliptic_curve as EC
import hashlib
import random
from secrets import randbits
from datetime import datetime
def str_xor(str1, str2):
    ans = ''
    for i in range(len(str1)):
        if str1[i] != str2[i]:
            ans += '1'
        else:
            ans += '0'
    return ans


# point to string
def pts(t):
    return str(t[0]) + str(t[1])


# random message generation
def rmg(n):
    msg = ''
    for i in range(n):
        msg += random.choice(['0', '1'])
    return msg


class KGC(object):

    def __init__(self, n, m):
        self.curve = None
        self.P = None
        self.q = None
        self.__msk = None
        self.P_pub = None
        self.ID_length = n
        self.msg_length = m
        self.parameters_gen()

    def parameters_gen(self):
        self.curve = EC.secp256r1()
        self.P = self.curve.generator
        self.q = self.curve.order
        self.__msk = randbits(256) % self.q
        self.P_pub = self.curve.scalar_multiplication(self.__msk, self.P)

    def H1(self, period, point_1, point_2):
        h = hashlib.sha512()
        h.update(period.encode() + pts(point_1).encode() + pts(point_2).encode())
        return bin(int(h.hexdigest(), 16))[2:self.ID_length + 2]

    def H2(self, pid, point_1, point_2, point_3):
        h = hashlib.sha512()
        h.update(pid.encode() + pts(point_1).encode() + pts(point_2).encode() + pts(point_3).encode())
        return int(h.hexdigest(), 16) % self.q

    def H3(self, pid, point_1, point_2):
        h = hashlib.sha512()
        h.update(pid.encode() + pts(point_1).encode() + pts(point_2).encode())
        return bin(int(h.hexdigest(), 16))[2:self.msg_length + 2]

    def H4(self, B, point_1, point_2):
        h = hashlib.sha512()
        h.update(B.encode() + pts(point_1).encode() + pts(point_2).encode())
        return bin(int(h.hexdigest(), 16))[2:self.msg_length + 2]

    def H5(self, pid, point_1, point_2, m, point_3, T):
        h = hashlib.sha512()
        h.update(pid.encode() + pts(point_1).encode() + pts(point_2).encode() + m.encode() + pts(
            point_3).encode() + T.encode())
        return int(h.hexdigest(), 16) % self.q

    def _partial_key_compute(self, RID, X):
        period = '20251231'
        temp = self.curve.scalar_multiplication(self.__msk, X)
        h_s_1 = self.H1(period, self.P_pub, temp)
        PID = str_xor(RID, h_s_1)
        a = randbits(256) % self.q
        A = self.curve.scalar_multiplication(a, self.P)
        h_s_2 = self.H2(PID, X, A, self.P_pub)
        y = a + self.__msk * h_s_2
        t = datetime.now()
        return (PID, period, A, y, t)


class public_para(object):
    def __init__(self, KGC):
        self.sys = KGC


class User(object):
    def __init__(self, para):
        self.psk = randbits(256) % para.sys.q
        self.RID = rmg(para.sys.ID_length)
        self.ppk = para.sys.curve.scalar_multiplication(self.psk, para.sys.P)
        self.u = randbits(256) % para.sys.q
        self.U = para.sys.curve.scalar_multiplication(self.u, para.sys.P)
        self.Tag = randbits(256) % para.sys.q
        self.TAG = para.sys.curve.scalar_multiplication(self.Tag, para.sys.P)

    def full_key_compute(self, para, partial_key):
        period = partial_key[1]
        temp = para.sys.curve.scalar_multiplication(self.psk, para.sys.P_pub)
        h_s_1 = para.sys.H1(period, para.sys.P_pub, temp)
        PID_1 = str_xor(self.RID, h_s_1)
        if PID_1 != partial_key[0]:
            print('ERROR: pseudo name incorrect')
            return
        h_s_2 = para.sys.H2(partial_key[0], self.ppk, partial_key[2], para.sys.P_pub)
        left = para.sys.curve.scalar_multiplication(partial_key[3], para.sys.P)
        right = para.sys.curve.add_points(partial_key[2], para.sys.curve.scalar_multiplication(h_s_2, para.sys.P_pub))
        if left != right:
            print("ERROR: partial key incorrect")
            return
        self.fsk = (self.psk, partial_key[3])
        self.fpk = (self.ppk, partial_key[2])
        self.PID = PID_1

    def offline_signcrypt(self, Receiver, para):
        PID_r = Receiver.PID
        P_pub = para.sys.P_pub
        X_r = Receiver.fpk[0]
        A_r = Receiver.fpk[1]
        h_r_2 = para.sys.H2(PID_r, X_r, A_r, P_pub)
        temp = para.sys.curve.add_points(para.sys.curve.add_points(X_r, A_r),
                                         para.sys.curve.scalar_multiplication(h_r_2, P_pub))
        W_r = para.sys.curve.scalar_multiplication(self.u, temp)
        return (self.u, self.U, W_r)

    def one_to_one_signcryption(self, Msg, Receiver, offline_Msg, para):
        W_r = offline_Msg[2]
        PID_r = Receiver.PID
        B_r = para.sys.H3(PID_r, self.U, W_r, len(Msg))
        c_r = str_xor(B_r, Msg)
        T = str(datetime.now())
        h_s = para.sys.H5(self.PID, self.fpk[0], self.fpk[1], Msg, self.TAG, T)
        val = offline_Msg[0] + h_s * (self.fsk[0] + self.fsk[1])
        return (self.PID, val, c_r, self.U, T,self.TAG)

    def one_to_many_signcryption(self, Receiver_list, Msg_list, offline_msg_list, para):
        C = []
        c_list = []
        s = ''
        for i in range(0, len(Msg_list)):
            W = offline_msg_list[i][2]
            B = para.sys.H3(Receiver_list[i].PID, self.U, W)
            c = str_xor(B, Msg_list[i])
            c_list.append(c)
            temp = para.sys.H4(B, self.U, W)
            val = temp + c
            C.append(val)
            s += val
        T = str(datetime.now())
        h_s = para.sys.H5(self.PID, self.fpk[0], self.fpk[1], s, self.TAG, T)
        val = self.u + h_s * (self.fsk[0] + self.fsk[1]) + self.Tag
        return (self.PID, val, C, self.U, T,self.TAG)

    def one_to_many_unsigncrypt(self, Ciphertext, para, fpk):
        U = Ciphertext[3]
        TAG = Ciphertext[5]
        W = para.sys.curve.scalar_multiplication((self.fsk[0] + self.fsk[1]), U)
        B = para.sys.H3(self.PID, U, W)
        s = ''
        for element in Ciphertext[2]:
            s += element
        h_s = para.sys.H5(Ciphertext[0], fpk[0], fpk[1], s, TAG, Ciphertext[4])
        h_2_s = para.sys.H2(Ciphertext[0], fpk[0], fpk[1], para.sys.P_pub)
        left = para.sys.curve.scalar_multiplication(Ciphertext[1], para.sys.P)
        right = para.sys.curve.add_points(para.sys.curve.add_points(fpk[0], fpk[1]),
                                          para.sys.curve.scalar_multiplication(h_2_s, para.sys.P_pub))
        temp1 = para.sys.curve.scalar_multiplication(h_s, right)
        temp1 = para.sys.curve.add_points(temp1, U)
        right = para.sys.curve.add_points(temp1, TAG)
        if right != left:
            print("ERROR")  #signature verification or cross-domain tag verification fails
            return
        mark = para.sys.H4(B, TAG, W)
        c = ''
        for element in Ciphertext[2]:
            if mark == element[:para.sys.msg_length]:
                c = element[para.sys.msg_length:]
        m = str_xor(c, B)
        return m

    def aggregation_unsigncrypt(self, C_list, fpk_list, para):
        P = para.sys.P
        m_list = []
        cnt = 0
        left = 0
        right = (0, 0)
        for C in C_list:
            U = C[3]
            TAG = C[5]
            PID = C[0]
            n = self.fsk[0] + self.fsk[1]
            W = para.sys.curve.scalar_multiplication(n, U)
            B = para.sys.H3(self.PID, U, W)
            m = str_xor(B, C[2])
            m_list.append(m)
            left += C[1]
            X = fpk_list[cnt][0]
            A = fpk_list[cnt][1]
            h = para.sys.H5(PID, X, A, m, TAG, C[4])
            h_2 = para.sys.H2(PID, X, A, para.sys.P_pub)
            temp1 = para.sys.curve.scalar_multiplication(h, para.sys.curve.add_points(para.sys.curve.add_points(X, A),
                                                                                      para.sys.curve.scalar_multiplication(
                                                                                          h_2, para.sys.P_pub)))
            temp1 = para.sys.curve.add_points(temp1, U)
            temp1 = para.sys.curve.add_points(temp1, TAG)
            if right == (0, 0):
                right = temp1
            else:
                right = para.sys.curve.add_points(temp1, right)
            cnt += 1
        left = para.sys.curve.scalar_multiplication(left, P)
        if left == right:
            return m_list
        else:
            print("Verification failed, please verify message one by one.")
            return




