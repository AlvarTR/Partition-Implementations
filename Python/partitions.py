#part.py: memoized version
import sys
import time
import operator

#Paralelo
##import threading
##import multiprocessing as mp
##from multiprocessing.pool import ThreadPool
##from concurrent.futures.thread import ThreadPoolExecutor
##from concurrent.futures.process import ProcessPoolExecutor
##import concurrent.futures

LIM = 5000
pmem = [1] + ([0]*LIM)

def p(n):
    if n < 0:
        return 0
    if pmem[n] != 0:
        return pmem[n]
    signLoop = (operator.pos, operator.neg)
    sign = signLoop[0] #sign = 1
    res = 0
    for k in range(1, n+1):
        p1 = n - (k*((3*k)-1)//2)
        if p1 >= 0:
           if pmem[p1] == 0:
               pmem[p1] = p(p1)

        p2 = p1 - k
        if p2 >= 0:
            if pmem[p2] == 0:
                pmem[p2] = p(p2)

        term = p(p1) + p(p2)
        res += sign(term) #res += sign*term
        sign = signLoop[k%2] #sign = -sign
    return res


def particionesOlvidando(n):
    return calculaMatrizOlvidando((), n, n, n)[-1][-1]

def calculaMatrizOlvidando(buffer, usando, libres, max):
    #print(buffer, usando, libres, max)
    #print()

    if usando == 0:
        if libres == 0:
            return ([], [1])

    if buffer == ():
        if libres < 0:
            return calculaMatrizOlvidando((), usando-1, max, max)
        return calculaMatrizOlvidando(
                calculaMatrizOlvidando((), usando, libres-1, max),
                usando, libres, max)


    primero = buffer[0]
    segundo = buffer[1].copy()

    if libres == 0:
        return (segundo, [1])

    if usando < 2:
        valor = 1
    else:
        valor = primero[libres]
        if usando <= libres:
            valor += segundo[-usando]

    segundo.append(valor)
    return (primero, segundo)

def particionesCola(n):
    return calculaMatrizCola( ([],[]), n, n, n )[-1][-1]

def calculaMatrizCola(buffer, usando, libres, max):
    #print(buffer, usando, libres, max)
    #print()
    if usando == 0:
        if libres == -1:
            return buffer

    primero = buffer[0]
    segundo = buffer[1].copy()

    if libres < 0:
        return calculaMatrizCola( (segundo, [1]), usando-1, max-1, max )


    if (max - usando) < 2:
        valor = 1
    else:
        valor = primero[-libres-1]
        if usando >= libres:
            valor += segundo[usando-max]

    segundo.append(valor)
    return calculaMatrizCola( (primero, segundo), usando, libres-1, max )


def particionesIter(n):
    if n < 0:
        return 0

    dimensionMatriz = n+1
    filaActual = [1] * dimensionMatriz

    for usados in range(2, dimensionMatriz):
        filaGuardada = filaActual
        filaActual = [1, 1] + [-1]*(dimensionMatriz-2)
        for libres in range(2, dimensionMatriz):
            valor = filaGuardada[libres]
            if usados <= libres:
                valor += filaActual[libres-usados]
            filaActual[libres] = valor

    return filaActual[-1]



def todasPartHastaLimite():
    print("LIM:", LIM)
    for n in range(0, LIM+1):
        if n%100 == 0:
            print(n, p(n))
    print("")

""" Conocimiento descubierto en Haskell """
"""
def numerosPentagonales (maxPent):
    positivo = 1
    if positivo > maxPent:
        return
    yield positivo

    for contador in range(1, maxPent):
        negativo = positivo + contador
        if (negativo > maxPent):
            break
        yield negativo

        positivo += 3*contador + 1
        if (positivo > maxPent):
            break
        yield positivo
"""
def numerosPentagonales (maxPent):
    positivo = 0
    contador = 0

    while contador < maxPent: # Para maxPent > 0, es como un while True
        positivo += 3*contador + 1
        if (positivo > maxPent):
            return
        yield positivo

        contador += 1

        negativo = positivo + contador
        if (negativo > maxPent):
            return
        yield negativo



def particionesPentaVector (n):
    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    particiones = [1]

    for subN in range(1, n+1):
        sumaPentagonales = 0

        for i, pent in enumerate(numerosPentagonales(subN)):
            particion = subN - pent
            sumaPentagonales += sumaOResta[i%4](particiones[particion])

        particiones.append(sumaPentagonales)

    return particiones[-1]

def particionesPentaVectorActualizando (n):
    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    particiones = [1] * (n+1)

    for subN in range(1, n+1):
        sumaPentagonales = 0

        for i, pent in enumerate(numerosPentagonales(subN)):
            particion = subN - pent
            sumaPentagonales += sumaOResta[i%4](particiones[particion])

        particiones[subN] = sumaPentagonales

    return particiones[-1]


def indexNumOrLower(list, number):
    bottom = -1
    top = len(list)
    middle = (top+bottom) // 2

    while bottom != middle and top != middle:
        valueInTheMiddle = list[middle]

        if valueInTheMiddle == number:
            return middle
        elif valueInTheMiddle < number:
            bottom = middle
        elif valueInTheMiddle > number:
            top = middle

        middle = (top+bottom) // 2

    return middle

def particionesPentaVectorOpt(n):
    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    pentagonales = list(numerosPentagonales(n))
    particiones = [1]

    for subN in range(1, n+1):
        sumaPentagonales = 0
        indice = indexNumOrLower(pentagonales, subN)
        pentagonalesSubN = pentagonales[:indice+1]

        #<paralelizable>
        sumaParcial = 0
        for i, pent in enumerate(pentagonalesSubN, 0):
            particion = subN - pent
            sumaParcial += sumaOResta[i%4](particiones[particion])
        #</paralelizable>

        sumaPentagonales += sumaParcial
        particiones.append(sumaPentagonales)

    return particiones[-1]

def particionesPentaVectorReOpt(n):
    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    pentagonales = list(enumerate(numerosPentagonales(n))) # Lista de nodos pentagonales (i, pent)

    particiones = [1] # particiones[0] = 1
    pentagonalesSubN = [] # Va recogiendo nodos pentagonales segun hacen falta
    for subN in range(1, n+1):
        lenPsubN = len(pentagonalesSubN)
        # Si aun no se han recogido todos los pentagonales, y el siguiente pentagonal es igual a subN
        if lenPsubN < len(pentagonales) and pentagonales[lenPsubN][1] == subN:
            # Recoge el siguiente nodo pentagonal
            pentagonalesSubN.append(pentagonales[lenPsubN])

        sumaPentagonales = 0 # Suma total
        #<paralelizable>
        sumaParcial = 0 # Variable intermediaria que permite paralelizar
        for i, pent in pentagonalesSubN:
            particion = subN - pent # Calcula el indice de la particion necesaria
            sumaParcial += sumaOResta[i%4](particiones[particion]) # Suma o resta p("particion") (ya calculada anteriormente)
        #</paralelizable>

        sumaPentagonales += sumaParcial # Recogida de variables intermediarias
        particiones.append(sumaPentagonales) # particion[subN] = sumaPentagonales

    return particiones[-1] # Devuelve la ultima particion calculada, p(n)

def particionesPentaVectorGen(n): # Comparable a opt en tiempo, pero con menos consumo de memoria (O(n*sqrt(n)) vs O(n*sqrt(n)*2))
    def nextNodo(generador):
        try:
            return next(generador) # Genera el siguiente nodo
        except StopIteration:
            return () # Si no hay mas, devuelve un nodo vacio = ()

    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    pentagonales = enumerate(numerosPentagonales(n)) # Generador de nodos pentagonales (i, pent)
    nextPentagonal = 0 # next(pentagonales) nunca sera 0; inicializacion
    nextPentagonal = nextNodo(pentagonales)

    particiones = [1] # particiones[0] = 1
    pentagonalesSubN = [] # Va recogiendo nodos pentagonales segun hacen falta
    for subN in range(1, n+1):
        # Si aun no se han recogido todos los nodos pentagonales, y el siguiente pentagonal es igual a subN
        if nextPentagonal and nextPentagonal[1] == subN:
            # Recoge el siguiente nodo pentagonal
            pentagonalesSubN.append(nextPentagonal)
            # Genera el siguiente pentagonal
            nextPentagonal = nextNodo(pentagonales)

        sumaPentagonales = 0 # Suma total
        #<paralelizable>
        sumaParcial = 0 # Variable intermediaria que permite paralelizar
        for i, pent in pentagonalesSubN:
            particion = subN - pent # Calcula el indice de la particion necesaria
            sumaParcial += sumaOResta[i%4](particiones[particion]) # Suma o resta p("particion") (ya calculada anteriormente)
        #</paralelizable>

        sumaPentagonales += sumaParcial # Recogida de variables intermediarias
        particiones.append(sumaPentagonales) # particion[subN] = sumaPentagonales

    return particiones[-1] # Devuelve la ultima particion calculada, p(n)


def particionesPentaVectorNodo(n): # Comparable a opt en tiempo, pero con menos consumo de memoria (O(n*sqrt(n)) vs O(n*sqrt(n)*2))
    def nextNodo(generador):
        try:
            return next(generador) # Genera el siguiente nodo
        except StopIteration:
            return () # Si no hay mas, devuelve un nodo vacio = ()

    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    pentagonales = ( (sumaOResta[i%4], penta) for (i, penta) in enumerate(numerosPentagonales(n)) ) # Generador de nodos pentagonales (signo, pent)

    nextPentagonal = nextNodo(pentagonales) # Generamos el primer nodo pentagonal
    pentagonalesSubN = [] # Recoge nodos pentagonales segun hacen falta
    particiones = [1] # particiones[0] = 1
    lenParticiones = 1 # Buffer de len(particiones)
    while lenParticiones <= n:
        # Si aun no se han recogido todos los nodos pentagonales, y el siguiente pentagonal es igual a lenParticiones
        if nextPentagonal and nextPentagonal[1] == lenParticiones:
            # Recoge el siguiente nodo pentagonal
            pentagonalesSubN.append(nextPentagonal)
            # Genera el siguiente pentagonal
            nextPentagonal = nextNodo(pentagonales)

        sumaPentagonales = 0
        for signo, pent in pentagonalesSubN:
            particion = lenParticiones - pent # Calcula el indice de la particion necesaria
            sumaPentagonales += signo(particiones[particion]) # Suma o resta p("particion") (ya calculado por prog dinamica) al acumulador

        particiones.append(sumaPentagonales) # particion[subN] = sumaPentagonales de pentagonalesSubN en ese momento
        lenParticiones += 1 # Aumenta el tamano, aumenta el buffer

    return particiones[-1] # Devuelve la ultima particion calculada, p(n)



def sumaParcialPentagonales(particiones, nodosPentagonales):
    n = len(particiones)

    sumaParcial = 0
    for signo, pent in nodosPentagonales:
        particion = n - pent # Calcula el indice de la particion necesaria
        sumaParcial += signo(particiones[particion]) # Suma o resta p("particion") (ya calculado por prog dinamica) al acumulador
    return sumaParcial


def particionesPentaVectorParalelizable(n): # Comparable a opt en tiempo, pero con menos consumo de memoria (O(n*sqrt(n)) vs O(n*sqrt(n)*2))
    def nextNodo(generador):
        try:
            return next(generador) # Genera el siguiente nodo
        except StopIteration:
            return () # Si no hay mas, devuelve un nodo vacio = ()

    sumaOResta = (operator.pos, operator.pos, operator.neg, operator.neg)
    pentagonales = ( (sumaOResta[i%4], penta) for (i, penta) in enumerate(numerosPentagonales(n)) ) # Generador de nodos pentagonales (signo, pent)

    nextPentagonal = nextNodo(pentagonales) # Generamos el primer nodo pentagonal
    pentagonalesSubN = [] # Recoge nodos pentagonales segun hacen falta
    particiones = [1] # particiones[0] = 1
    while len(particiones) <= n:
        # Si aun no se han recogido todos los nodos pentagonales, y el siguiente pentagonal es igual a lenParticiones
        if nextPentagonal and nextPentagonal[1] == len(particiones):
            # Recoge el siguiente nodo pentagonal
            pentagonalesSubN.append(nextPentagonal)
            # Genera el siguiente pentagonal
            nextPentagonal = nextNodo(pentagonales)

        sumaPentagonales = 0
        numCortes = 2
        tamanoCorte = (len(pentagonalesSubN) // numCortes)+1
        for corte in range(numCortes):
            inicio = corte*tamanoCorte
            fin = inicio + tamanoCorte
            pentagonalesCortados = pentagonalesSubN[inicio:fin]
            #<paralelizable> (no importa el orden, a la suma le es indiferente)
            #   Para paralelizar igual es necesaria "sumaPentagonales" como memoria compartida (bloqueando cada vez que se actualice)
            sumaParcial = sumaParcialPentagonales(particiones, pentagonalesCortados)
            # TODO en paralelo Consolidar sumaPentagonales para que se guarde correctamente
            sumaPentagonales += sumaParcial # Recogida de variables intermedias
            #</paralelizable>

        particiones.append(sumaPentagonales) # particion[subN] = sumaPentagonales de pentagonalesSubN en ese momento

    return particiones[-1] # Devuelve la ultima particion calculada, p(n)

def particionesUnaLinea(n):
    nPartition = 1
    if n < 2:
        return nPartition

    dp = [1 for _ in range(n-1)]
    for used in range(2, n+1):
        for i in range(used, len(dp)):
            dp[i] += dp[i-used]
        nPartition += dp.pop()
    return nPartition

def particionesUnaLineaWhile(n):
    nPartition = 1
    if n < 2:
        return nPartition

    dp = [1]*(n-1)
    used = 2
    while used < len(dp):
        for i in range(used, len(dp)):
            dp[i] += dp[i-used]
        nPartition += dp.pop()
        used += 1
    return nPartition + sum(dp)

if __name__ == "__main__":
    #todasPartHastaLimite()
    #sys.setrecursionlimit(128*128*128)

    #print( particionesCola(LIM) )
    #print( calculaMatrizCola( ([],[]), LIM, LIM, LIM ) )

    #print( particionesOlvidando(LIM) )
    #print( calculaMatrizOlvidando( (), LIM, LIM, LIM ) )

    #chrono = time.time()
    #valor = particionesIter(LIM)
    #print( "Iter de", LIM, valor, time.time() - chrono )

    #chrono = time.time()
    #valor = p(LIM)
    #print( "Ramanujan de", LIM, valor, time.time() - chrono )
    for i in range(1, 3):
        thisLim = i*LIM

        """
        chrono = time.time()
        valor = particionesPentaVectorNodo(thisLim)
        print( "particionesPentaVectorNodo de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVectorParalelizable(thisLim)
        print( "particionesPentaVectorParalelizable de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVectorReOpt(thisLim)
        print( "particionesPentaVectorReOpt de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVectorGen(thisLim)
        print( "particionesPentaVectorGen de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVectorOpt(thisLim)
        print( "particionesPentaVectorOpt de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVector(thisLim)
        print( "PentaVector de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesPentaVectorActualizando(thisLim)
        print( "PentaVectorActualizando de", thisLim, valor, time.time() - chrono )
        print()
        """
        # Tiempo O(n^2 / 4), Espacio O(n)
        """
        chrono = time.time()
        valor = particionesUnaLinea(thisLim)
        print( "particionesUnaLinea de", thisLim, valor, time.time() - chrono )
        print()
        """
        """
        chrono = time.time()
        valor = particionesUnaLineaWhile(thisLim)
        print( "particionesUnaLineaWhile de", thisLim, valor, time.time() - chrono )
        print()
        """

        print("\n")
