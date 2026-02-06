#DANIEL ROLDAN SERRANO

# para esta actividad necesitamos la anterior (cuerpos_finitos.py)
# completa, pero quitando las funciones de factorización en anillo_fp_x
# y en anillo_fq_x, ya que las implementaremos aquí (no se olviden de
# quitarlas)
import cuerpos_finitos as cf

# square-free factorization
# input: fpx --> anillo_fp_x
# input: f --> polinomio fabricado por fpx (objeto opaco) no nulo
# output: g = producto de los factores irreducibles mónicos de f, es decir,
# si f = c * f1^e1 * f2^e2 * ... * fr^er con los fi irreducibles mónicos
# distintos entre si, ei >= 1, c en fp, entonces g = f1 * f2 * ... * fr
def sqfree_fact_fpx(fpx, f):
    f = fpx.quitar_ceros(f)
    if fpx.es_cero(f):
        raise ValueError("El polinomio f no puede ser cero.")
    if fpx.grado(f) == 0:
        return fpx.monic(f)

    df = fpx.derivada(f)

    # Caso 1: Potencia p-ésima pura
    if fpx.es_cero(df):
        p = fpx.fp.p
        g_coeffs = []
        for i in range(0, len(f), p):
            g_coeffs.append(f[i])
        g = fpx.elem_de_tuple(tuple(g_coeffs))
        return sqfree_fact_fpx(fpx, g)

    # Caso 2: Caso Mixto 
    G = fpx.gcd(f, df)
    w = fpx.div(f, G)
    
    rest = f
    while True:
        common = fpx.gcd(rest, w)
        if fpx.grado(common) == 0: # Si es 1
            break
        rest = fpx.div(rest, common)
        
    # Procesar el resto
    if fpx.grado(rest) > 0:
        p = fpx.fp.p
        root_coeffs = []
        for i in range(0, len(rest), p):
            root_coeffs.append(rest[i])
        root_rest = fpx.elem_de_tuple(tuple(root_coeffs))
        
        part_p = sqfree_fact_fpx(fpx, root_rest)
        
        total = fpx.mult(w, part_p)
        return fpx.monic(total)
    else:
        return fpx.monic(w)

# distinct-degree factorization
# input: fpx --> anillo_fp_x
# input: g --> polinomio de fpx (objeto opaco) que es producto de factores
# irreducibles mónicos distintos cada uno con multiplicidad uno
# output: [h1, h2, ..., hr], donde hi = producto de los factores irreducibles
# mónicos de h de grado = i, el último hr debe ser no nulo y por supuesto
# g = h1 * h2 * ... * hr
def didegr_fact_fpx(fpx, g):
    h_star = fpx.quitar_ceros(g)
    
    if fpx.grado(h_star) == 0:
        return []

    res = []
    x = (fpx.fp.cero(), fpx.fp.uno()) 
    p = fpx.fp.p
    d = 1
    
    while fpx.grado(h_star) >= 2 * d:
        exp = pow(p, d)
        val = fpx.pot_mod(x, exp, h_star)
        term = fpx.suma(val, fpx.inv_adit(x))
        h_d = fpx.gcd(term, h_star)
        
        res.append(fpx.monic(h_d)) 
        
        if not fpx.es_uno(h_d):
            h_star = fpx.div(h_star, h_d)
            h_star = fpx.quitar_ceros(h_star)
        d += 1

    if fpx.grado(h_star) > 0:
        degree_rem = fpx.grado(h_star)
        while len(res) < degree_rem - 1:
            res.append(fpx.uno()) 
        res.append(fpx.monic(h_star))
        
    return res

# equal-degree factorization
# input: fpx --> anillo_fp_x (supondremos p impar)
# input: r --> int
# input: h --> polinomio de fpx (objeto opaco) que es producto de factores
# irreducibles mónicos distintos de grado r con multiplicidad uno
# output: [u1, ..., us], donde h = u1 * u2* ... * us y los ui son irreducibles
# mónicos de grado = r
def eqdegr_fact_fpx(fpx, r, h):
    h = fpx.quitar_ceros(h)
    
    if fpx.es_uno(h):
        return []
        
    if fpx.grado(h) == r:
        return [fpx.monic(h)]

    p = fpx.fp.p
    deg_h = fpx.grado(h)

    while True:
        a = fpx.random_pol(deg_h - 1)
        if fpx.es_cero(a):
            continue
        g = fpx.gcd(a, h)
        if not fpx.es_uno(g) and fpx.grado(g) < deg_h:
            return eqdegr_fact_fpx(fpx, r, g) + eqdegr_fact_fpx(fpx, r, fpx.div(h, g))
        
        exp = (pow(p, r) - 1) // 2
        pow_val = fpx.pot_mod(a, exp, h)
        term = fpx.suma(pow_val, fpx.inv_adit(fpx.uno()))
        g = fpx.gcd(term, h)
        if not fpx.es_uno(g) and fpx.grado(g) < deg_h:
            lista_g = eqdegr_fact_fpx(fpx, r, g)
            lista_resto = eqdegr_fact_fpx(fpx, r, fpx.div(h, g))
            return lista_g + lista_resto

# multiplicidad de factor irreducible mónico
# input: fpx --> anillo_fp_x
# input: f --> polinomio de fpx (objeto opaco) no nulo
# input: u --> polinomio irreducible mónico (objeto opaco) de grado >= 1
# output: multiplicidad de u como factor de f, es decir, el entero e >= 0
# mas grande tal que u^e | f
def multiplicidad_fpx(fpx, f, u):
    e = 0
    curr = f
    while True:
        q, r = fpx.divmod(curr, u)
        if fpx.es_cero(r):
            e += 1
            curr = q
        else:
            break
    return e

# factorización de Cantor-Zassenhaus
# input: fpx --> anillo_fp_x (supondremos p impar)
# input: f --> polinomio de fpx (objeto opaco)
# output: [(f1,e1), ..., (fr,er)] donde f = c * f1^e1 * ... * fr^er es la
# factorización completa de f en irreducibles mónicos fi con multiplicidad
# ei >= 1 y los fi son distintos entre si y por supuesto c es el coeficiente
# principal de f
def fact_fpx(fpx, f):                     # mantener esta implementación
    g = sqfree_fact_fpx(fpx, f)
    h = didegr_fact_fpx(fpx, g)
    irreducibles = []
    for r in range(len(h)):
        if fpx.grado(h[r]) > 0:
            irreducibles += eqdegr_fact_fpx(fpx, r+1, h[r])
    factorizacion = []
    for u in irreducibles:
        e = multiplicidad_fpx(fpx, f, u)
        factorizacion += [(u,e)]
    return factorizacion

# esta linea es para añadir la función de factorización de Cantor-Zassenhaus
# como un método de la clase anillo_fp_x
cf.anillo_fp_x.factorizar = fact_fpx

# square-free factorization
# input: fqx --> anillo_fq_x
# input: f --> polinomio fabricado por fqx (objeto opaco) no nulo
# output: g = producto de los factores irreducibles mónicos de f, es decir,
# si f = c * f1^e1 * f2^e2 * ... * fr^er con los fi irreducibles mónicos
# distintos entre si, ei >= 1, c en fq, entonces g = f1 * f2 * ... * fr
def sqfree_fact_fqx(fqx, f):
    f = fqx.quitar_ceros(f)
    if fqx.es_cero(f):
        raise ValueError("El polinomio f no puede ser cero.")
    if fqx.grado(f) == 0:
        return fqx.monic(f)

    df = fqx.derivada(f)

    # Caso 1: Potencia p-ésima pura
    if fqx.es_cero(df):
        p = fqx.fq.fp.p
        q = fqx.fq.q
        exp_root = q // p
        g_coeffs = []
        grado_f = fqx.grado(f)
        for i in range(0, grado_f // p + 1):
            idx = i * p
            if idx < len(f):
                coeff = f[idx]
                root = fqx.fq.pot(coeff, exp_root)
                g_coeffs.append(root)
            else:
                g_coeffs.append(fqx.fq.cero())          
        g = fqx.elem_de_tuple(tuple(g_coeffs))
        return sqfree_fact_fqx(fqx, g)

    # Caso 2: Caso Mixto 
    G = fqx.gcd(f, df)
    w = fqx.div(f, G)
    
    # Limpiar w de f
    rest = f
    while True:
        common = fqx.gcd(rest, w)
        if fqx.grado(common) == 0:
            break
        rest = fqx.div(rest, common)
        
    # Procesar el resto
    if fqx.grado(rest) > 0:
        p = fqx.fq.fp.p
        q = fqx.fq.q
        exp_root = q // p
        root_coeffs = []
        grado_rest = fqx.grado(rest)
        
        for i in range(0, grado_rest // p + 1):
            idx = i * p
            if idx < len(rest):
                coeff = rest[idx]
                root = fqx.fq.pot(coeff, exp_root)
                root_coeffs.append(root)
            else:
                root_coeffs.append(fqx.fq.cero())
                
        root_rest = fqx.elem_de_tuple(tuple(root_coeffs))
        
        part_p = sqfree_fact_fqx(fqx, root_rest)
        
        total = fqx.mult(w, part_p)
        return fqx.monic(total)
    else:
        return fqx.monic(w)

# distinct-degree factorization
# input: fqx --> anillo_fq_x
# input: g --> polinomio de fqx (objeto opaco) que es producto de factores
# irreducibles mónicos distintos cada uno con multiplicidad uno
# output: [h1, h2, ..., hr], donde hi = producto de los factores irreducibles
# mónicos de h de grado = i, el último hr debe ser no nulo y por supuesto
# g = h1 * h2 * ... * hr
def didegr_fact_fqx(fqx, g):
    h_star = fqx.quitar_ceros(g)
    
    if fqx.grado(h_star) == 0:
        return []

    res = []
    x = (fqx.fq.cero(), fqx.fq.uno())
    q = fqx.fq.q
    d = 1
    
    while fqx.grado(h_star) >= 2 * d:
        exp = pow(q, d)
        val = fqx.pot_mod(x, exp, h_star)
        term = fqx.suma(val, fqx.inv_adit(x))
        h_d = fqx.gcd(term, h_star)
        
        res.append(fqx.monic(h_d))
        
        if not fqx.es_uno(h_d):
            h_star = fqx.div(h_star, h_d)
            h_star = fqx.quitar_ceros(h_star)  
        d += 1
        
    if fqx.grado(h_star) > 0:
        degree_rem = fqx.grado(h_star)
        while len(res) < degree_rem - 1:
            res.append(fqx.uno())
        res.append(fqx.monic(h_star))
    
    return res

# equal-degree factorization
# input: fqx --> anillo_fq_x (supondremos q impar)
# input: r --> int
# input: h --> polinomio de fqx (objeto opaco) que es producto de factores
# irreducibles mónicos distintos de grado r con multiplicidad uno
# output: [u1, ..., us], donde h = u1 * u2* ... * us y los ui son irreducibles
# mónicos de grado = r
def eqdegr_fact_fqx(fqx, r, h):
    h = fqx.quitar_ceros(h)

    if fqx.es_uno(h):
        return []
        
    if fqx.grado(h) == r:
        return [fqx.monic(h)]

    q = fqx.fq.q
    deg_h = fqx.grado(h)

    while True:
        coeffs = []
        for _ in range(deg_h):
            coeffs.append(fqx.fq.aleatorio())
        a = fqx.elem_de_tuple(tuple(coeffs))
        
        if fqx.es_cero(a):
            continue
            
        g = fqx.gcd(a, h)
        if not fqx.es_uno(g) and fqx.grado(g) < deg_h:
            return eqdegr_fact_fqx(fqx, r, g) + eqdegr_fact_fqx(fqx, r, fqx.div(h, g))
            
        exp = (pow(q, r) - 1) // 2
        val = fqx.pot_mod(a, exp, h)
        term = fqx.suma(val, fqx.inv_adit(fqx.uno()))
        g = fqx.gcd(term, h)
        if not fqx.es_uno(g) and fqx.grado(g) < deg_h:
            return eqdegr_fact_fqx(fqx, r, g) + eqdegr_fact_fqx(fqx, r, fqx.div(h, g))

# multiplicidad de factor irreducible mónico
# input: fqx --> anillo_fq_x
# input: f --> polinomio de fqx (objeto opaco) no nulo
# input: u --> polinomio irreducible mónico (objeto opaco) de grado >= 1
# output: multiplicidad de u como factor de f, es decir, el entero e >= 0
# mas grande tal que u^e | f
def multiplicidad_fqx(fqx, f, u):
    e = 0
    curr = f
    while True:
        q, r = fqx.divmod(curr, u)
        if fqx.es_cero(r):
            e += 1
            curr = q
        else:
            break
    return e

# factorización de Cantor-Zassenhaus
# input: fqx --> anillo_fq_x (supondremos q impar)
# input: f --> polinomio de fqx (objeto opaco)
# output: [(f1,e1), ..., (fr,er)] donde f = c * f1^e1 * ... * fr^er es la
# factorización completa de f en irreducibles mónicos fi con multiplicidad
# ei >= 1 y los fi son distintos entre si y por supuesto c es el coeficiente
# principal de f
def fact_fqx(fqx, f):                     # mantener esta implementación
    g = sqfree_fact_fqx(fqx, f)
    h = didegr_fact_fqx(fqx, g)
    irreducibles = []
    for r in range(len(h)):
        if fqx.grado(h[r]) > 0:
            irreducibles += eqdegr_fact_fqx(fqx, r+1, h[r])
    factorizacion = []
    for u in irreducibles:
        e = multiplicidad_fqx(fqx, f, u)
        factorizacion += [(u,e)]
    return factorizacion

# esta linea es para añadir la función de factorización de Cantor-Zassenhaus
# como un método de la clase anillo_fq_x
cf.anillo_fq_x.factorizar = fact_fqx
