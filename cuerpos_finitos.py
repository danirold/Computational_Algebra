#DANIEL ROLDAN SERRANO

# Se deben implementar 4 clases: cuerpo_fp, anillo_fp_x, cuerpo_fq, anillo_fq_x
# respetando el esqueleto de abajo. Se pueden añadir funciones auxiliares, pero
# las indicadas deben estar. Los elementos de cada uno de estos cuerpos/anillos
# son objetos opacos.

import random

def es_primo(p):
    i = 2
    while pow(i, 2) <= p:
        if p%i == 0: 
            return False
        i += 1
    return True

class cuerpo_fp:
    def __init__(self, p): # construye el cuerpo de p elementos Fp = Z/pZ
        if p <= 1 or not es_primo(p):
            raise ValueError('p no es un primo mayor o igual que 2')
        self.p = p

    def cero(self):        # devuelve el elemento 0
        return 0
    
    def uno(self):         # devuelve el elemento 1
        return 1
    
    def elem_de_int(self, n): # fabrica el elemento dado por la clase de n
        return n % self.p
    
    def elem_de_str(self, s): # fabrica el elemento a partir de un string (parser)
        return self.elem_de_int(int(s))
        
    def conv_a_int(self, a):  # devuelve un entero entre 0 y p-1
        return self.elem_de_int(int(a))
        
    def conv_a_str(self, a):  # pretty-printer
        return str(self.elem_de_int(a))
        
    def suma(self, a, b):     # a+b
        return self.elem_de_int(a + b)
        
    def inv_adit(self, a):    # -a
        return self.elem_de_int(-a)
        
    def mult(self, a, b):     # a*b
        return self.elem_de_int(a * b)
        
    def pot(self, a, k):      # a^k (k entero)
        if k == 0:
            return self.uno()
        elif k % 2 == 0:
            aux = self.pot(a, k // 2)
            return self.mult(aux, aux)
        else:
            return self.mult(self.pot(a, k - 1), a)
        
    def inv_mult(self, a):    # a^(-1)
        if a == 0:
            raise ValueError('El 0 no se puede invertir')
        return self.pot(a, self.p - 2)
        
    def es_cero(self, a):     # a == 0
        return self.elem_de_int(a) == self.cero()
        
    def es_uno(self, a):      # a == 1
        return self.elem_de_int(a) == self.uno()
        
    def es_igual(self, a, b): # a == b
        return self.elem_de_int(a) == self.elem_de_int(b)
        
    def aleatorio(self):      # fabrica un elemento aleatorio con prob uniforme
        return random.randint(0, self.p - 1)
        
    def tabla_suma(self):     # devuelve la matriz de pxp (lista de listas) de la suma
        return [[self.suma(i, j) for j in range(self.p)] for i in range(self.p)]
        
    def tabla_mult(self):     # devuelve la matriz de pxp (lista de listas) de la mult
        return [[self.mult(i, j) for j in range(self.p)] for i in range(self.p)]
        
    def tabla_inv_adit(self): # devuelve una lista de long p con los inv_adit
        inv_adit = []
        for i in range(0, self.p):
            inv_adit.append(self.inv_adit(i))
        return inv_adit
        
    def tabla_inv_mult(self): # devuelve una lista de long p con los inv_mult (en el índice 0 pone un '*')
        inv_mult = ['*']  #Ponemos un '*' en el indice 0
        for i in range(1, self.p):
            inv_mult.append(self.inv_mult(i))
        return inv_mult
        
    def cuadrado_latino(self, a): # cuadrado latino a*i+j (con a != 0)
        if a % self.p == 0:
            raise ValueError("a = 0 y no es posible")
        return [[self.suma(self.mult(a, i), j) for j in range(self.p)] for i in range(self.p)]


class anillo_fp_x:
    def __init__(self, fp, var='x'): # construye el anillo Fp[var]
        self.fp = fp
        self.var = var
        
    def cero(self):                 # 0
        return (self.fp.cero(),)
        
    def uno(self):                  # 1
        return (self.fp.uno(),)
        
    def quitar_ceros(self, a):
        res = list(a)
        while len(res) > 1 and self.fp.es_cero(res[-1]):
            res.pop()
        if len(res) == 0:
            res = [self.fp.cero()]
        return tuple(res)
        
    def elem_de_tuple(self, a):     # fabrica un polinomio a partir de la tupla (a0, a1, ...)
        res = [self.fp.elem_de_int(elem) for elem in a]
        return self.quitar_ceros(res)
        
    def elem_de_int(self, a):       # fabrica un polinomio a partir de los dígitos de a en base p
        if a == 0:
            return (self.fp.cero(),)
        res = []
        p = self.fp.p
        while a > 0:
            res.append(self.fp.elem_de_int(a))
            a //= p
        return self.quitar_ceros(res)
        
    def elem_de_str(self, s):       # fabrica un polinomio a partir de un string (parser)
        nums = s.split(",")
        coeficientes = [self.fp.elem_de_int(int(n.strip())) for n in nums]
        return self.quitar_ceros(coeficientes)
        
    def conv_a_tuple(self, a):      # devuelve la tupla de coeficientes
        return tuple(a)
        
    def conv_a_int(self, a):        # devuelve el entero correspondiente al polinomio
        if isinstance(a, int):
            return a
        res = 0
        p = self.fp.p
        for i in range(0, len(a)):
            res += a[i] * pow(p, i)
        return res
        
    def conv_a_str(self, a):        # pretty-printer
        a = self.quitar_ceros(a)
        if self.es_cero(a):
            return "0"

        grado = len(a) - 1
        parts = []
        
        for i in range(grado, -1, -1):
            coef = a[i]
            if coef == 0:
                continue

            term_str = ""
            sign = ""

            if parts: 
                sign = "+"

            if i == 0:
                term_str = str(coef)
            else: 
                if coef == 1:
                    term_str = self.var
                else:
                    term_str = str(coef) + "*" + self.var
                
                if i > 1:
                    term_str += "^" + str(i)

            parts.append(sign + term_str)

        result = "".join(parts)
        
        result = result.replace("+-", "-") 
        
        if result.startswith('+'):
            result = result[1:]

        return result if result else "0"
            
    def suma(self, a, b):           # a+b
        n = max(len(a), len(b))
        a = a + (self.fp.cero(),) * (n - len(a))
        b = b + (self.fp.cero(),) * (n - len(b))
        res = [self.fp.suma(a[i], b[i]) for i in range(n)]
        return self.quitar_ceros(res)
        
    def inv_adit(self, a):          # -a
        res = [self.fp.inv_adit(a[i]) for i in range(len(a))]
        return self.quitar_ceros(res)
        
    def mult(self, a, b):           # a*b
        a = self.quitar_ceros(a)
        b = self.quitar_ceros(b)
        res = [self.fp.cero()] * (len(a) + len(b) - 1)
        for i in range(len(a)):
            for j in range(len(b)):
                res[i + j] = self.fp.suma(res[i + j], self.fp.mult(self.conv_a_int(a[i]), self.conv_a_int(b[j])))
        return self.quitar_ceros(res)
        
    def mult_por_escalar(self, a, e): # a*e (con e en Z/pZ)
        res = [self.fp.mult(a[i], e) for i in range(len(a))]
        return self.quitar_ceros(res)
        
    def divmod(self, a, b):        # devuelve q,r tales que a=bq+r y deg(r)<deg(b)
        return (self.div(a, b), self.mod(a, b))
        
    def div(self, a, b):           # q
        f = list(self.quitar_ceros(a))
        g = list(self.quitar_ceros(b))
        if self.es_cero(g):
            raise ZeroDivisionError("División por polinomio cero")
        if len(f) < len(g):
            return self.cero()
        q_len = len(f) - len(g) + 1
        q = [self.fp.cero()] * q_len
        lider_g = g[-1]
        inv_lider_g = self.fp.inv_mult(lider_g)
        for k in range(q_len - 1, -1, -1):
            coef_f = f[-1]
            factor = self.fp.mult(coef_f, inv_lider_g)
            q[k] = factor
            for i in range(len(g)):
                idx = i + k
                ter_a_restar = self.fp.mult(g[i], factor)
                f[idx] = self.fp.suma(f[idx], self.fp.inv_adit(ter_a_restar))    
            f.pop()
        return tuple(self.quitar_ceros(q))
        
    def mod(self, a, b): # r 
        f = list(self.quitar_ceros(a))
        g = list(self.quitar_ceros(b))
        if self.es_cero(g):
            raise ZeroDivisionError("División por polinomio cero")
        if len(f) < len(g):
            return tuple(f)
        lider_g = g[-1]
        inv_lider_g = self.fp.inv_mult(lider_g)
        while len(f) >= len(g) and not self.es_cero(f): 
            coef_f = f[-1]
            deg_diff = len(f) - len(g)
            factor = self.fp.mult(coef_f, inv_lider_g)
            for i in range(len(g)):
                idx = i + deg_diff      
                ter_a_restar = self.fp.mult(g[i], factor)      
                f[idx] = self.fp.suma(f[idx], self.fp.inv_adit(ter_a_restar))      
            f.pop()
        return tuple(self.quitar_ceros(f))
        
    def grado(self, a):            # deg(a)
        return len(self.quitar_ceros(a)) - 1
        
    def gcd(self, a, b):  # devuelve g = gcd(a,b) mónico
        f = self.quitar_ceros(a)
        g = self.quitar_ceros(b)
        if self.es_cero(g):
            return f
        if self.es_cero(f):
            return g
        while not self.es_cero(g):
            r = self.mod(f, g)
            f, g = g, r
        if self.es_cero(f):
            return self.cero()
        inv_cp = self.fp.inv_mult(f[-1])
        monico = [self.fp.mult(c, inv_cp) for c in f]
        return self.quitar_ceros(monico)

    def gcd_ext(self, a, b):       # devuelve g,x,y tales que g=ax+by, g=gcd(a,b) mónico
        x0, x1 = self.uno(), self.cero()
        y0, y1 = self.cero(), self.uno()
        f, g = a, b
        while not self.es_cero(g):
            q = self.div(f, g)
            r = self.mod(f, g)
            f, g = g, r
            x0, x1 = x1, self.suma(x0, self.inv_adit(self.mult(q, x1)))
            y0, y1 = y1, self.suma(y0, self.inv_adit(self.mult(q, y1)))

        if self.es_cero(f): 
            return f, x0, y0
            
        inv_cp = self.fp.inv_mult(f[-1])
        g_monico = [self.fp.mult(c, inv_cp) for c in f]
        x_monico = [self.fp.mult(c, inv_cp) for c in x0]
        y_monico = [self.fp.mult(c, inv_cp) for c in y0]
        return tuple(self.quitar_ceros(g_monico)), tuple(self.quitar_ceros(x_monico)), tuple(self.quitar_ceros(y_monico))
    
    def inv_mod(self, a, b):       # devuelve x tal que ax = 1 mod b
        g, x, y = self.gcd_ext(a, b)
        if not self.es_uno(g):
            raise ValueError("No existe inverso: gcd(a,b) != 1")
        return self.mod(x, b)
    
    def pot_mod(self, a, k, b):    # a^k mod b
        if k == 0:
            return self.uno()
        if k % 2 == 0:
            aux = self.pot_mod(a, k // 2, b)
            return self.mod(self.mult(aux, aux), b)
        else:
            return self.mod(self.mult(self.pot_mod(a, k - 1, b), a), b)
        
    def es_cero(self, a):          # a == 0
        return self.quitar_ceros(a) == self.cero()
    
    def es_uno(self, a):           # a == 1
        return self.quitar_ceros(a) == self.uno()
    
    def es_igual(self, a, b):      # a == b
        return self.elem_de_tuple(self.quitar_ceros(a)) == self.elem_de_tuple(self.quitar_ceros(b))
    
    def factorizar_ent(self, n):
        fact = []
        p = 2
        while n > 1:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            if e != 0:
                fact.append((p, e))
            p += 1
        return fact

    def es_irreducible(self, f):   # test de irreducibilidad de Rabin
        f = self.quitar_ceros(f)
        if self.es_cero(f):
            raise ValueError('No esta definida la irreducibilidad de 0')
        grado = self.grado(f)
        if grado <= 1:
            return True
        fact = self.factorizar_ent(grado)
        x = (self.fp.cero(), self.fp.uno())  # x
        g = self.pot_mod(x, pow(self.fp.p, grado), f)
        if not self.es_igual(g, x):
            return False
        for (d, e) in fact:
            exp = pow(self.fp.p, grado // d)
            g = self.pot_mod(x, exp, f)
            g = self.suma(g, self.inv_adit(x))  # x^{p^{grado/d}} - x
            h = self.gcd(g, f)
            if not self.es_uno(h):
                return False
        return True
    
    def derivada(self, f):
        f = self.quitar_ceros(f)
        if len(f) <= 1:
            return self.cero()
        res = []
        for i in range(1, len(f)):
            res.append(self.fp.elem_de_int(f[i] * i))
        return tuple(self.quitar_ceros(res))
        
    def random_pol(self, grado): 
        res = [self.fp.aleatorio() for _ in range(grado + 1)]
        return self.quitar_ceros(res)
    
    def monic(self, f):
        f = self.quitar_ceros(f)
        if self.es_cero(f):
            return self.cero()
        coef_principal = f[-1]
        if self.fp.es_uno(coef_principal):
            return f
        try:
            inverso_lider = self.fp.inv_mult(coef_principal)
        except ValueError:
            raise ValueError("El coeficiente principal no tiene inverso multiplicativo.")
        res = self.mult_por_escalar(f, inverso_lider)
        return tuple(self.quitar_ceros(res))
        

class cuerpo_fq:
    def __init__(self, fp, g, var='a'): # construye el cuerpo Fp[var]/<g(var)>, g es objeto fabricado por fp
        self.fp = fp
        self.fp_x = anillo_fp_x(self.fp)
        self.g = g
        self.q = pow(self.fp.p, self.fp_x.grado(g))
        self.var = var
    
    def cero(self):                # 0
        return (self.fp.cero(),)
       
    def uno(self):                 # 1
        return (self.fp.uno(),)

    def reducir(self, f):
        return self.fp_x.mod(list(f), list(self.g))
    
    def elem_de_tuple(self, a):    # fabrica elemento a partir de tupla de coeficientes
        res = self.fp_x.elem_de_tuple(a)
        return self.reducir(res)
        
    def elem_de_int(self, a):      # fabrica elemento a partir de entero
        res = self.fp_x.elem_de_int(a)
        return self.reducir(res)
        
    def elem_de_str(self, s):      # fabrica elemento parseando string
        res = self.fp_x.elem_de_str(s)
        return self.reducir(res)

    def conv_a_tuple(self, a):     # devuelve tupla de coeficientes sin ceros "extra"
        res = self.fp_x.conv_a_tuple(a)
        return self.reducir(res)
        
    def conv_a_int(self, a):       # devuelve el entero correspondiente
        res = self.fp_x.conv_a_int(a)
        return res
        
    def conv_a_str(self, a):       # pretty-printer
        a_red = self.reducir(a)
        s = self.fp_x.conv_a_str(a_red)
        s = s.replace('x', self.var)
        return s
        
    def suma(self, a, b):          # a+b
        suma = self.fp_x.suma(a,b)
        return self.reducir(suma)
        
    def inv_adit(self, a):         # -a
        inv_adit = self.fp_x.inv_adit(a)
        return self.reducir(inv_adit)
        
    def mult(self, a, b):          # a*b
        mul = self.fp_x.mult(a,b)  
        return self.reducir(mul)

    def mult_por_escalar(self, a, e): # a*e (con e en Z/pZ)
        mul_esc = self.fp_x.mult_por_escalar(a, e)
        return tuple(self.reducir(mul_esc))
    
    def pot(self, a, k):           # a^k (k entero)
        return self.fp_x.pot_mod(a,k, self.g)
        
    def inv_mult(self, a):         # a^(-1)
        if self.es_cero(a):
            raise ValueError("El 0 no se puede invertir")
        inv_mul = self.pot(a, self.q - 2)
        return self.reducir(inv_mul)
        
    def es_cero(self, a):          # a == 0
        return a == self.cero()
        
    def es_uno(self, a):           # a == 1
        return a == self.uno()
        
    def es_igual(self, a, b):      # a == b
        return self.fp_x.es_igual(a,b)
        
    def aleatorio(self):           # devuelve un elemento aleatorio con prob uniforme
        res = self.fp_x.random_pol(self.fp_x.grado(self.g) - 1)
        return self.reducir(res)
        
    def tabla_suma(self):          # matriz de qxq correspondiente a la suma (con la notación int)
        suma = []
        for i in range(self.q):
            fila = []
            for j in range(self.q):
                a = self.elem_de_int(i)
                b = self.elem_de_int(j)
                fila.append(self.conv_a_int(self.suma(a, b)))
            suma.append(fila)
        return suma
        
    def tabla_mult(self):          # matriz de qxq correspondiente a la mult (con la notación int)
        mul = []
        for i in range(self.q):
            fila = []
            for j in range(self.q):
                a = self.elem_de_int(i)
                b = self.elem_de_int(j)
                fila.append(self.conv_a_int(self.mult(a, b)))
            mul.append(fila)
        return mul
        
    def tabla_inv_adit(self):      # lista de inv_adit (con la notación int)
        inv_adit = []
        for i in range(self.q):
            a = self.elem_de_int(i)
            inv_adit.append(self.conv_a_int(self.inv_adit(a)))
        return inv_adit
        
    def tabla_inv_mult(self):      # lista de inv_mult (con la notación int)
        inv_mul = ['*']
        for i in range(self.q):
            a = self.elem_de_int(i)
            inv_mul.append(self.conv_a_int(self.inv_mult(a)))
        return inv_mul
        
    def cuadrado_latino(self, a):  # cuadrado latino para a != 0 (con notación int)
        if self.es_cero(a):
            raise ValueError("a = 0 y no puede serlo")
        
        q = self.q
        
        return [[ self.conv_a_int( self.suma( self.mult(a, self.elem_de_int(i)), self.elem_de_int(j)) ) for j in range(q) ] for i in range(q)]


class anillo_fq_x:
    def __init__(self, fq, var='x'): # Fq[var], var debe ser distinta que la de fq
        self.fq = fq
        self.var = var
        
    def cero(self):                # 0
        return (self.fq.cero(),)
        
    def uno(self):                 # 1
        return (self.fq.uno(),)

    def quitar_ceros(self, a):
        res = list(a)
        while len(res) > 1 and self.fq.es_cero(res[-1]):
            res.pop()
        if len(res) == 0 or self.fq.es_cero(res[0]) and len(res) == 1:
            return self.cero()
        return tuple(res)
    
    def elem_de_tuple(self, a):
        res = []
        for elem in a:
            res.append(self.fq.elem_de_tuple(elem))
        return tuple(self.quitar_ceros(res))
        
    def elem_de_int(self, a):
        res = []
        while a > 0:
            res.append(self.fq.elem_de_int(a % self.fq.q))
            a //= self.fq.q
        return tuple(self.quitar_ceros(res))
        
    def elem_de_str(self, s):
        nums = s.split(",")
        coeficientes = [self.fq.elem_de_int(int(n.strip())) for n in nums]
        return tuple(self.quitar_ceros(coeficientes))
        
    def conv_a_tuple(self, a):
        return tuple(a)
        
    def conv_a_int(self, a):
        res = 0
        for i in range(0, len(a)):
            res += self.fq.conv_a_int(a[i])*pow(self.fq.q, i)
        return res
        
    def conv_a_str(self, a):
        pol = self.quitar_ceros(a)
        if self.es_cero(pol):
            return "0"

        grado = len(pol) - 1
        parts = []

        for i in range(grado, -1, -1):
            coef_fq = pol[i]
            if self.fq.es_cero(coef_fq):
                continue

            coef_str = self.fq.conv_a_str(coef_fq) 
            term_str = ""
            sign = ""
            
            if parts:
                if not coef_str.startswith('-'):
                    sign = "+"
                
            if i == 0:
                term_str = coef_str
            else: 
                needs_paren = ('+' in coef_str) or ('-' in coef_str and not coef_str.startswith('-'))

                if self.fq.es_uno(coef_fq):
                    term_str = self.var
                elif needs_paren:
                    term_str = "(" + coef_str + ")*" + self.var
                else:
                    term_str = coef_str + "*" + self.var

                if i > 1:
                    term_str += "^" + str(i)

            parts.append(sign + term_str)

        result = "".join(parts)
        
        result = result.replace("+-", "-")
        if result.startswith('+'):
            result = result[1:]

        return result if result else "0"
        
    def suma(self, a, b):
        n = max(len(a), len(b))
        a = a + self.cero() * (n - len(a))
        b = b + self.cero() * (n - len(b))
        res = []
        for i in range(0, n):
            res.append(self.fq.suma(a[i], b[i]))
        return tuple(self.quitar_ceros(res))
        
    def inv_adit(self, a):
        res = []
        for i in range(0, len(a)):
            res.append(self.fq.inv_adit(a[i]))
        return tuple(self.quitar_ceros(res))
        
    def mult(self, a, b):
        res = [self.fq.cero()]*(len(a) + len(b) - 1)
        for i in range(0,len(a)):
            for j in range(0, len(b)):
                res[i + j] = self.fq.suma(self.fq.mult(a[i], b[j]), res[i + j])
        return tuple(self.quitar_ceros(res))
        
    def mult_por_escalar(self, a, e):
        res = [self.fq.cero()]*len(a)
        for i in range(0,len(a)):
            res[i] = self.fq.mult(a[i], e)
        return tuple(self.quitar_ceros(res))
        
    def divmod(self, a, b):
        return (self.div(a,b), self.mod(a,b))
        
    def div(self, a, b):
        "Divide a entre b en Fq[x], devolviendo el cociente."
        f = list(self.quitar_ceros(a))
        g = list(self.quitar_ceros(b))
        if self.es_cero(g):
            raise ZeroDivisionError("División por polinomio cero")
        if len(f) < len(g):
            return self.cero()
        q_len = len(f) - len(g) + 1
        q = [self.fq.cero()] * q_len
        lider_g = g[-1]
        inv_lider_g = self.fq.inv_mult(lider_g)
        for k in range(q_len - 1, -1, -1):
            coef_f = f[-1]
            factor = self.fq.mult(coef_f, inv_lider_g)
            q[k] = factor
            for i in range(len(g)):
                idx = i + k
                ter_a_restar = self.fq.mult(g[i], factor)
                f[idx] = self.fq.suma(f[idx], self.fq.inv_adit(ter_a_restar))
            f.pop()
        return tuple(self.quitar_ceros(q))
        
    def mod(self, a, b):
        f = list(self.quitar_ceros(a))
        g = list(self.quitar_ceros(b))
        if self.es_cero(g):
            raise ZeroDivisionError("División por polinomio cero")
        if len(f) < len(g):
            return tuple(f)
        lider_g = g[-1]
        inv_lider_g = self.fq.inv_mult(lider_g)
        while len(f) >= len(g) and not self.es_cero(f):
            coef_f = f[-1]
            deg_diff = len(f) - len(g)
            factor = self.fq.mult(coef_f, inv_lider_g)
            for i in range(len(g)):
                idx = i + deg_diff
                ter_a_restar = self.fq.mult(g[i], factor)
                f[idx] = self.fq.suma(f[idx], self.fq.inv_adit(ter_a_restar))
            f.pop()
        return tuple(self.quitar_ceros(f))
        
    def grado(self, a):
        return len(a) - 1
        
    def gcd(self, a, b):
        "Calcula el mcd de dos polinomios a, b en Fq[x], devolviendo un polinomio mónico."
        f = self.quitar_ceros(a)
        g = self.quitar_ceros(b)
        # Casos triviales
        if self.es_cero(f) and self.es_cero(g):
            return self.cero()
        if self.es_cero(f):
            return tuple(self.quitar_ceros(g))
        if self.es_cero(g):
            return tuple(self.quitar_ceros(f))
        # Algoritmo de Euclides
        while not self.es_cero(g):
            r = self.mod(f, g)
            r = self.quitar_ceros(r)
            f, g = g, r
        f = self.quitar_ceros(f)
        if self.es_cero(f):
            return self.cero()
        # Normalizar a mónico
        coef_principal = f[-1]
        inv_cp = self.fq.inv_mult(coef_principal)
        monico = [self.fq.mult(c, inv_cp) for c in f]
        return tuple(self.quitar_ceros(monico))
        
    def gcd_ext(self, a, b):
        x0, x1 = self.uno(), self.cero() 
        y0, y1 = self.cero(), self.uno() 
        f, g = a, b 
        while g != self.cero(): 
            q = self.div(f, g) # cociente 
            r = self.mod(f, g) # resto 
            f, g = g, r 
            x0, x1 = x1, self.suma(x0, self.inv_adit(self.mult(q, x1))) 
            y0, y1 = y1, self.suma(y0, self.inv_adit(self.mult(q, y1))) # Normalizar g para que sea monico 

        if self.es_cero(f):
            return f, x0, y0
        
        coef_prin = f[-1] # coeficiente principal
        inv_cp = self.fq.inv_mult(coef_prin) 
        g_monico = tuple(self.fq.mult(c, inv_cp) for c in f) 
        x_monico = tuple(self.fq.mult(c, inv_cp) for c in x0) 
        y_monico = tuple(self.fq.mult(c, inv_cp) for c in y0) 
        return g_monico, x_monico, y_monico
        
    def inv_mod(self, a, b):
        g, x, y = self.gcd_ext(a, b)
        if g != self.uno(): #no existe inverso si no son coprimos
            raise ValueError("No existe inverso: gcd(a,b) != 1")
        return self.mod(x, b) # x mod b es el inverso
        
    def pot_mod(self, a, k, b):
        if (k == 0):
            return self.uno()
        elif (k % 2 == 0):
            aux = self.pot_mod(a, k // 2, b)
            return self.mod(self.mult(aux, aux), b)
        else:
            return self.mod(self.mult(self.pot_mod(a, k - 1, b), a), b)
        
    def es_cero(self, a):
        return self.quitar_ceros(a) == self.cero()
        
    def es_uno(self, a):
        return self.quitar_ceros(a) == self.uno()
        
    def es_igual(self, a, b):
        return self.elem_de_tuple(self.quitar_ceros(a)) == self.elem_de_tuple(self.quitar_ceros(b))

    def factorizar_ent(self, n):
        fact = []
        p = 2
        while n > 1:
            e = 0
            while n%p == 0:
                n //= p
                e += 1
            if e != 0:
                fact.append((p,e))
            p += 1
        return fact
    
    def es_irreducible(self, f):
        f = self.quitar_ceros(f)
        if self.es_cero(f):
            raise ValueError('No esta definida la irreducibilidad de 0') 
        grado = self.grado(f)
        if grado <= 1:
            return True
        # Raíz X
        x = (self.fq.cero(), self.fq.uno())
        q = self.fq.q
        # Test de primalidad: X^(q^grado) mod f == X mod f
        g = self.pot_mod(x, pow(q, grado), f)
        if not self.es_igual(g, x):
            return False
        # Test de divisibilidad: gcd(X^(q^(grado/d)) - X, f) == 1 para todo divisor primo d de grado
        fact = self.factorizar_ent(grado)
        for (d, e) in fact:
            exp = pow(q, grado // d)
            # Calculamos X^(q^(grado/d)) mod f
            g = self.pot_mod(x, exp, f)
            # Calculamos X^(q^(grado/d)) - X mod f
            # X^(q^(grado/d)) - X = X^(q^(grado/d)) + (-X)
            g_minus_x = self.suma(g, self.inv_adit(x))
            h = self.gcd(g_minus_x, f)
            if not self.es_uno(h):
                return False
        return True

    def derivada(self, f):
        f = self.quitar_ceros(f)
        if len(f) <= 1:
            return self.cero()
        res = []
        for i in range(1, len(f)):
            res.append(self.fq.mult_por_escalar(f[i], i))
        return tuple(self.quitar_ceros(res))

    def monic(self, f):
        f = self.quitar_ceros(f)
        if self.es_cero(f):
            return f
        coef_principal = f[-1]
        if self.fq.es_uno(coef_principal):
            return f
        try:
            inverso_lider = self.fq.inv_mult(coef_principal)
        except ValueError:
            raise ValueError("El coeficiente principal no tiene inverso (¿es 0?).")
        res = self.mult_por_escalar(f, inverso_lider)
        return self.quitar_ceros(res)
    