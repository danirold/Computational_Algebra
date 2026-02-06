#DANIEL ROLDAN SERRANO

# para esta actividad necesitamos la primera (cuerpos_finitos.py) completa
import cuerpos_finitos as cf

# input: fpx -> anillo_fp_x
# input: f -> polinomio (objeto opaco creado por fpx)
# input: g -> polinomio (objeto opaco creado por fpx)
# output: f*g calculado usando el método de Karatsuba
def fp_x_mult_karatsuba(fpx, f, g):
    f = fpx.quitar_ceros(f)
    g = fpx.quitar_ceros(g)

    if len(f) <= 1 or len(g) <= 1:
        return fpx.mult(f, g)

    n = max(len(f), len(g))
    m = n // 2

    f_low = f[:m]
    f_high = f[m:]
    g_low = g[:m]
    g_high = g[m:]

    if not f_low: f_low = fpx.cero()
    if not f_high: f_high = fpx.cero()
    if not g_low: g_low = fpx.cero()
    if not g_high: g_high = fpx.cero()

    p0 = fp_x_mult_karatsuba(fpx, f_low, g_low)
    p2 = fp_x_mult_karatsuba(fpx, f_high, g_high)
    
    sum_f = fpx.suma(f_low, f_high)
    sum_g = fpx.suma(g_low, g_high)
    p1 = fp_x_mult_karatsuba(fpx, sum_f, sum_g)

    mid = fpx.suma(p1, fpx.inv_adit(p2))
    mid = fpx.suma(mid, fpx.inv_adit(p0))

    zeros_2m = (fpx.fp.cero(),) * (2 * m)
    zeros_m = (fpx.fp.cero(),) * m
    
    term_high = zeros_2m + p2
    term_mid = zeros_m + mid
    
    res = fpx.suma(term_high, term_mid)
    res = fpx.suma(res, p0)

    return fpx.quitar_ceros(res)

# añadimos esta función a la clase (sin sobreescribir la que ya teníamos)
cf.anillo_fp_x.mult_fast = fp_x_mult_karatsuba

# input: fp -> cuerpo_fp
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fp (primera columna de una
#    matriz de Toeplitz inferior T de nxn)
# input: b -> tupla de longitud n de elementos de fp (vector)
# output: T*b -> tupla de longitud n de elementos de fp (vector)
# se debe utilizar fp_x_mult_karatsuba internamente
def fp_toep_inf_vec(fp, n, a, b):
    fpx = cf.anillo_fp_x(fp)
    
    pol_a = fpx.elem_de_tuple(a)
    pol_b = fpx.elem_de_tuple(b)
    
    res_poly = fp_x_mult_karatsuba(fpx, pol_a, pol_b)

    res_list = list(res_poly)
    
    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        padding = [fp.cero()] * (n - len(res_list))
        return tuple(res_list + padding)

# input: fp -> cuerpo_fp
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fp (primera fila de una
#    matriz de Toeplitz superior T de nxn)
# input: b -> tupla de longitud n de elementos de fp (vector)
# output: T*b -> tupla de longitud n de elementos de fp (vector)
# se debe utilizar fp_x_mult_karatsuba internamente
def fp_toep_sup_vec(fp, n, a, b):
    fpx = cf.anillo_fp_x(fp)
    
    pol_a = fpx.elem_de_tuple(a)
    
    pol_b = fpx.elem_de_tuple(b[::-1])
    
    res_poly = fp_x_mult_karatsuba(fpx, pol_a, pol_b)
    
    res_list = list(res_poly)
    
    if len(res_list) < n:
        res_list += [fp.cero()] * (n - len(res_list))
        
    relevant_coeffs = res_list[:n]
    
    return tuple(relevant_coeffs[::-1])

# input: fp -> cuerpo_fp
# input: n >= 1 (int)
# input: a -> tupla de longitud 2*n-1 de elementos de fp (primera fila de una
#    matriz de Toeplitz completa T de nxn seguida de la primera columna
#    excepto el elemento de la esquina)
# input: b -> tupla de longitud n de elementos de fp (vector)
# output: T*b -> tupla de longitud n de elementos de fp (vector)
# se debe utilizar fp_x_mult_karatsuba internamente
def fp_toep_vec(fp, n, a, b):
    fpx = cf.anillo_fp_x(fp)
    
    diag = (a[0],)
    row_part = a[1:n]     
    col_part = a[n:]       
    
    s_tuple = col_part[::-1] + diag + row_part
    
    pol_s = fpx.elem_de_tuple(s_tuple)
    pol_b = fpx.elem_de_tuple(b)
    
    res_poly = fp_x_mult_karatsuba(fpx, pol_s, pol_b)
    res_list = list(res_poly)
    
    limit_index = 2 * n - 1
    if len(res_list) < limit_index:
        res_list += [fp.cero()] * (limit_index - len(res_list))
        
    result_slice = res_list[n-1 : 2*n-1]
    
    return tuple(result_slice)

# input: fp -> cuerpo_fp
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fp (primera columna de una
#    matriz de Toeplitz inferior T de nxn)... suponemos a[0] != 0
# output: primera columna de T^(-1) -> tupla de longitud n de elementos de
#    fp (vector)
# utilizar un método recursivo que "divida el problema a la mitad"
# recordar que T^(-1) es también una matriz de Toeplitz inferior
def fp_toep_inf_inv(fp, n, a):
    if n == 1:
        inv_val = fp.inv_mult(a[0])
        return (inv_val,)

    k = (n + 1) // 2
    
    b_k_tuple = fp_toep_inf_inv(fp, k, a[:k])

    fpx = cf.anillo_fp_x(fp)
    
    pol_a = fpx.elem_de_tuple(a)
    pol_b_k = fpx.elem_de_tuple(b_k_tuple)
    
    prod_a_bk = fp_x_mult_karatsuba(fpx, pol_a, pol_b_k)
    
    dos = (fp.elem_de_int(2),) 
    factor = fpx.suma(dos, fpx.inv_adit(prod_a_bk))
    
    res_poly = fp_x_mult_karatsuba(fpx, pol_b_k, factor)
    
    res_list = list(res_poly)
    
    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        padding = [fp.cero()] * (n - len(res_list))
        return tuple(res_list + padding)

# input: fp -> cuerpo_fp
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fp (primera fila de una
#    matriz de Toeplitz superior T de nxn)... suponemos a[0] != 0
# output: primera fila de T^(-1) -> tupla de longitud n de elementos de
#    fp (vector)
# utilizar un método recursivo que "divida el problema a la mitad"
# recordar que T^(-1) es también una matriz de Toeplitz superior
def fp_toep_sup_inv(fp, n, a):
    if n == 1:
        inv_val = fp.inv_mult(a[0])
        return (inv_val,)

    k = (n + 1) // 2
    
    b_k_tuple = fp_toep_sup_inv(fp, k, a[:k])

    fpx = cf.anillo_fp_x(fp)
    
    pol_a = fpx.elem_de_tuple(a)
    pol_b_k = fpx.elem_de_tuple(b_k_tuple)
    
    prod_a_bk = fp_x_mult_karatsuba(fpx, pol_a, pol_b_k)
    
    dos = (fp.elem_de_int(2),)
    factor = fpx.suma(dos, fpx.inv_adit(prod_a_bk))
    
    res_poly = fp_x_mult_karatsuba(fpx, pol_b_k, factor)
    
    res_list = list(res_poly)
    
    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        padding = [fp.cero()] * (n - len(res_list))
        return tuple(res_list + padding)

# input: fpx -> anillo_fp_x
# input: f -> polinomio (objeto opaco creado por fpx)
# input: g -> polinomio no nulo (objeto opaco creado por fpx)
# output: q -> cociente
# output: r -> resto
# se cumple que f = g*q+r, r=0 o deg(r)<deg(g)
# reformular el problema en términos de matrices de Toeplitz y luego usar
# las funciones de arriba para obtener q y r
def fp_x_divmod(fpx, f, g):
    f = fpx.quitar_ceros(f)
    g = fpx.quitar_ceros(g)
    
    if fpx.es_cero(g):
        raise ZeroDivisionError("División por polinomio cero")
        
    deg_f = fpx.grado(f)
    deg_g = fpx.grado(g)
    
    if deg_f < deg_g:
        return (fpx.cero(), f)
        
    L = deg_f - deg_g + 1
    
    coeffs_f = list(f)
    coeffs_g = list(g)
    
    rev_f = coeffs_f[::-1]
    rev_g = coeffs_g[::-1]
    
    vec_g = rev_g[:L]
    if len(vec_g) < L:
        vec_g += [fpx.fp.cero()] * (L - len(vec_g))
        
    vec_f = rev_f[:L] 
    
    inv_col = fp_toep_inf_inv(fpx.fp, L, tuple(vec_g))
    
    coeffs_q_rev = fp_toep_inf_vec(fpx.fp, L, inv_col, tuple(vec_f))
    
    coeffs_q = list(coeffs_q_rev)[::-1]
    q = fpx.elem_de_tuple(tuple(coeffs_q))
    
    prod = fp_x_mult_karatsuba(fpx, g, q)
    r = fpx.suma(f, fpx.inv_adit(prod))

    q = fpx.quitar_ceros(q)
    r = fpx.quitar_ceros(r)
    
    return (q, r)

# añadimos esta función a la clase (sin sobreescribir la que ya teníamos)
cf.anillo_fp_x.divmod_fast = fp_x_divmod

# input: fp -> cuerpo_fp
# input: g -> elemento del grupo multiplicativo fp* de orden n (objeto opaco)
# input: k >= 0 tal que n = 2**k divide a p-1
# input: a -> tupla de longitud n de elementos de fp
# output: DFT_{n,g}(a) -> tupla de longitud n de elementos de fp
# utilizar el algoritmo de Cooley-Tuckey
def fp_fft(fp, g, k, a):
    if k == 0:
        return a
    
    even_coeffs = a[0::2]
    odd_coeffs = a[1::2]
    
    g_squared = fp.mult(g, g)
    
    r_even = fp_fft(fp, g_squared, k - 1, even_coeffs)
    r_odd = fp_fft(fp, g_squared, k - 1, odd_coeffs)
    
    n = len(a)
    half_n = n // 2
    res = [fp.cero()] * n
    
    w = fp.uno()
    
    for i in range(half_n):
        odd_term = fp.mult(w, r_odd[i])
        even_term = r_even[i]
        
        res[i] = fp.suma(even_term, odd_term)
        
        res[i + half_n] = fp.suma(even_term, fp.inv_adit(odd_term))
        
        w = fp.mult(w, g)
        
    return tuple(res)

# input: fp -> cuerpo_fp
# input: g -> elemento del grupo multiplicativo fp* de orden n (objeto opaco)
# input: k >= 0 tal que n = 2**k divide a p-1
# input: a -> tupla de longitud n de elementos de fp
# output: IDFT_{n,g}(a) -> tupla de longitud n de elementos de fp
# recordar que IDFT_{n,g} = n^(-1) * DFT_{n,g^(-1)}
def fp_ifft(fp, g, k, a):
    g_inv = fp.inv_mult(g)
    
    dft_result = fp_fft(fp, g_inv, k, a)
    
    n = 2**k  
    n_elem = fp.elem_de_int(n)
    n_inv = fp.inv_mult(n_elem)
    
    res = []
    for elem in dft_result:
        res.append(fp.mult(elem, n_inv))
        
    return tuple(res)

# input: fqx -> anillo_fq_x
# input: f -> polinomio (objeto opaco creado por fqx)
# input: g -> polinomio (objeto opaco creado por fqx)
# output: f*g calculado usando el método de Karatsuba
def fq_x_mult_karatsuba(fqx, f, g):
    f = fqx.quitar_ceros(f)
    g = fqx.quitar_ceros(g)

    if len(f) <= 1 or len(g) <= 1:
        return fqx.mult(f, g)

    n = max(len(f), len(g))
    m = n // 2

    f_low = f[:m]
    f_high = f[m:]
    g_low = g[:m]
    g_high = g[m:]

    if not f_low: f_low = fqx.cero()
    if not f_high: f_high = fqx.cero()
    if not g_low: g_low = fqx.cero()
    if not g_high: g_high = fqx.cero()

    p0 = fq_x_mult_karatsuba(fqx, f_low, g_low)
    p2 = fq_x_mult_karatsuba(fqx, f_high, g_high)
    
    sum_f = fqx.suma(f_low, f_high)
    sum_g = fqx.suma(g_low, g_high)
    p1 = fq_x_mult_karatsuba(fqx, sum_f, sum_g)

    mid = fqx.suma(p1, fqx.inv_adit(p2))
    mid = fqx.suma(mid, fqx.inv_adit(p0))

    zeros_2m = (fqx.fq.cero(),) * (2 * m)
    zeros_m = (fqx.fq.cero(),) * m
    
    term_high = zeros_2m + p2
    term_mid = zeros_m + mid
    
    res = fqx.suma(term_high, term_mid)
    res = fqx.suma(res, p0)

    return fqx.quitar_ceros(res)

# añadimos esta función a la clase (sin sobreescribir la que ya teníamos)
cf.anillo_fq_x.mult_fast = fq_x_mult_karatsuba

# input: fq -> cuerpo_fq
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fq (primera columna de una
#    matriz de Toeplitz inferior T de nxn)
# input: b -> tupla de longitud n de elementos de fq (vector)
# output: T*b -> tupla de longitud n de elementos de fq (vector)
# se debe utilizar fq_x_mult_karatsuba internamente
def fq_toep_inf_vec(fq, n, a, b):
    fqx = cf.anillo_fq_x(fq)

    pol_a = fqx.elem_de_tuple(a)
    pol_b = fqx.elem_de_tuple(b)
    
    res_poly = fq_x_mult_karatsuba(fqx, pol_a, pol_b)
    
    res_list = list(res_poly)
    
    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        padding = [fq.cero()] * (n - len(res_list))
        return tuple(res_list + padding)

# input: fq -> cuerpo_fq
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fq (primera fila de una
#    matriz de Toeplitz superior T de nxn)
# input: b -> tupla de longitud n de elementos de fq (vector)
# output: T*b -> tupla de longitud n de elementos de fq (vector)
# se debe utilizar fq_x_mult_karatsuba internamente
def fq_toep_sup_vec(fq, n, a, b):
    fqx = cf.anillo_fq_x(fq)
    
    pol_a = fqx.elem_de_tuple(a)
    
    pol_b = fqx.elem_de_tuple(b[::-1])
    
    res_poly = fq_x_mult_karatsuba(fqx, pol_a, pol_b)
    
    res_list = list(res_poly)
    
    if len(res_list) < n:
        res_list += [fq.cero()] * (n - len(res_list))
        
    relevant_coeffs = res_list[:n]
    
    return tuple(relevant_coeffs[::-1])

# input: fq -> cuerpo_fq
# input: n >= 1 (int)
# input: a -> tupla de longitud 2*n-1 de elementos de fq (primera fila de una
#    matriz de Toeplitz completa T de nxn seguida de la primera columna
#    excepto el elemento de la esquina)
# input: b -> tupla de longitud n de elementos de fq (vector)
# output: T*b -> tupla de longitud n de elementos de fq (vector)
# se debe utilizar fq_x_mult_karatsuba internamente
def fq_toep_vec(fq, n, a, b):
    fqx = cf.anillo_fq_x(fq)
    
    diag = (a[0],)
    row_part = a[1:n]
    col_part = a[n:]
    
    s_tuple = col_part[::-1] + diag + row_part
    
    pol_s = fqx.elem_de_tuple(s_tuple)
    pol_b = fqx.elem_de_tuple(b)
    
    res_poly = fq_x_mult_karatsuba(fqx, pol_s, pol_b)
    res_list = list(res_poly)
    
    limit_index = 2 * n - 1
    if len(res_list) < limit_index:
        res_list += [fq.cero()] * (limit_index - len(res_list))
        
    return tuple(res_list[n-1 : limit_index])

# input: fq -> cuerpo_fq
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fq (primera columna de una
#    matriz de Toeplitz inferior T de nxn)... suponemos a[0] != 0
# output: primera columna de T^(-1) -> tupla de longitud n de elementos de
#    fq (vector)
# utilizar un método recursivo que "divida el problema a la mitad"
# recordar que T^(-1) es también una matriz de Toeplitz inferior
def fq_toep_inf_inv(fq, n, a):
    if n == 1:
        return (fq.inv_mult(a[0]),)

    k = (n + 1) // 2
    b_k = fq_toep_inf_inv(fq, k, a[:k])

    fqx = cf.anillo_fq_x(fq)
    pol_a = fqx.elem_de_tuple(a)
    pol_b = fqx.elem_de_tuple(b_k)

    prod = fq_x_mult_karatsuba(fqx, pol_a, pol_b)
    
    dos = (fq.elem_de_int(2),)
    factor = fqx.suma(dos, fqx.inv_adit(prod))

    res_poly = fq_x_mult_karatsuba(fqx, pol_b, factor)
    res_list = list(res_poly)

    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        return tuple(res_list + [fq.cero()] * (n - len(res_list)))

# input: fq -> cuerpo_fq
# input: n >= 1 (int)
# input: a -> tupla de longitud n de elementos de fq (primera fila de una
#    matriz de Toeplitz superior T de nxn)... suponemos a[0] != 0
# output: primera fila de T^(-1) -> tupla de longitud n de elementos de
#    fq (vector)
# utilizar un método recursivo que "divida el problema a la mitad"
# recordar que T^(-1) es también una matriz de Toeplitz superior
def fq_toep_sup_inv(fq, n, a):
    if n == 1:
        return (fq.inv_mult(a[0]),)

    k = (n + 1) // 2
    b_k = fq_toep_sup_inv(fq, k, a[:k])

    fqx = cf.anillo_fq_x(fq)
    pol_a = fqx.elem_de_tuple(a)
    pol_b = fqx.elem_de_tuple(b_k)

    prod = fq_x_mult_karatsuba(fqx, pol_a, pol_b)
    
    dos = (fq.elem_de_int(2),)
    factor = fqx.suma(dos, fqx.inv_adit(prod))

    res_poly = fq_x_mult_karatsuba(fqx, pol_b, factor)
    res_list = list(res_poly)

    if len(res_list) >= n:
        return tuple(res_list[:n])
    else:
        return tuple(res_list + [fq.cero()] * (n - len(res_list)))

# input: fqx -> anillo_fq_x
# input: f -> polinomio (objeto opaco creado por fqx)
# input: g -> polinomio no nulo (objeto opaco creado por fqx)
# output: q -> cociente
# output: r -> resto
# se cumple que f = g*q+r, r=0 o deg(r)<deg(g)
# reformular el problema en términos de matrices de Toeplitz y luego usar
# las funciones de arriba para obtener q y r
def fq_x_divmod(fqx, f, g):
    f = fqx.quitar_ceros(f)
    g = fqx.quitar_ceros(g)
    
    if fqx.es_cero(g):
        raise ZeroDivisionError("División por polinomio cero")
        
    deg_f = fqx.grado(f)
    deg_g = fqx.grado(g)
    
    if deg_f < deg_g:
        return (fqx.cero(), f)
        
    L = deg_f - deg_g + 1
    
    coeffs_f = list(f)
    coeffs_g = list(g)
    
    rev_f = coeffs_f[::-1]
    rev_g = coeffs_g[::-1]
    
    vec_g = rev_g[:L]
    if len(vec_g) < L:
        vec_g += [fqx.fq.cero()] * (L - len(vec_g))
        
    vec_f = rev_f[:L]
    
    inv_col = fq_toep_inf_inv(fqx.fq, L, tuple(vec_g))
    
    coeffs_q_rev = fq_toep_inf_vec(fqx.fq, L, inv_col, tuple(vec_f))
    
    coeffs_q = list(coeffs_q_rev)[::-1]
    q = fqx.elem_de_tuple(tuple(coeffs_q))
    
    prod = fq_x_mult_karatsuba(fqx, g, q)
    r = fqx.suma(f, fqx.inv_adit(prod))
    
    q = fqx.quitar_ceros(q)
    r = fqx.quitar_ceros(r)

    return (q, r)

# añadimos esta función a la clase (sin sobreescribir la que ya teníamos)
cf.anillo_fq_x.divmod_fast = fq_x_divmod

# input: fq -> cuerpo_fq
# input: g -> elemento del grupo multiplicativo fq* de orden n (objeto opaco)
# input: k >= 0 tal que n = 2**k divide a q-1
# input: a -> tupla de longitud n de elementos de fq
# output: DFT_{n,g}(a) -> tupla de longitud n de elementos de fq
# utilizar el algoritmo de Cooley-Tuckey
def fq_fft(fq, g, k, a):
    if k == 0:
        return a

    even_coeffs = a[0::2]
    odd_coeffs = a[1::2]
    
    g_squared = fq.mult(g, g)
    
    r_even = fq_fft(fq, g_squared, k - 1, even_coeffs)
    r_odd = fq_fft(fq, g_squared, k - 1, odd_coeffs)
    
    n = len(a)
    half_n = n // 2
    res = [fq.cero()] * n
    
    w = fq.uno()
    
    for i in range(half_n):
        odd_term = fq.mult(w, r_odd[i])
        even_term = r_even[i]
        
        res[i] = fq.suma(even_term, odd_term)
        res[i + half_n] = fq.suma(even_term, fq.inv_adit(odd_term))
        
        w = fq.mult(w, g)
        
    return tuple(res)

# input: fq -> cuerpo_fq
# input: g -> elemento del grupo multiplicativo fq* de orden n (objeto opaco)
# input: k >= 0 tal que n = 2**k divide a p-1
# input: a -> tupla de longitud n de elementos de fq
# output: IDFT_{n,g}(a) -> tupla de longitud n de elementos de fq
# recordar que IDFT_{n,g} = n^(-1) * DFT_{n,g^(-1)}
def fq_ifft(fq, g, k, a):
    g_inv = fq.inv_mult(g)
    
    dft_result = fq_fft(fq, g_inv, k, a)
    
    n_val_int = 1 << k  
    
    n_val_fp = fq.fp.elem_de_int(n_val_int)
    n_inv_fp = fq.fp.inv_mult(n_val_fp)
    
    n_inv_fq = (n_inv_fp,)
    
    res = []
    for elem in dft_result:
        res.append(fq.mult(elem, n_inv_fq))
        
    return tuple(res)
