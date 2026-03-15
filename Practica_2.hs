{-
    Práctica 2 - Recursión Análisis Sintactico y Semantico
                 de LProp
    Profesor: Dr. Marco Vladimir Lemus Yañez
    Ayudante: Dr. Fernando Cruz Pineda
    Fecha: 14/03/2026 

    Integrantes del equipo:
    - Becerra Valencia César
    - Cortes Nava José Luis
    - Díaz Anavia Javier Omar
-}

-- 4.1 Análisis Sintáctico

data LProp = Var String
           | Not LProp
           | And LProp LProp
           | Or LProp LProp
           | Imp LProp LProp
           deriving (Show, Eq)

{-
    contarConectivos: Cuenta el número de conectivos lógicos en una fórmula dada.
    Los conectivos lógicos son: Not, And, Or, Imp. La función recorre la estructura de la fórmula
    y suma 1 por cada conectivo encontrado, además de contar los conectivos en las subfórmulas recursivamente.
-}
contarConectivos :: LProp -> Int
contarConectivos (Var _) = 0
contarConectivos (Not p) = 1 + contarConectivos p
contarConectivos (And p q) = 1 + contarConectivos p + contarConectivos q
contarConectivos (Or p q) = 1 + contarConectivos p + contarConectivos q
contarConectivos (Imp p q) = 1 + contarConectivos p + contarConectivos q

-- Definición de Interpretación como una lista de pares (variable, valor).
type Interpretacion = [(String, Bool)]

{-
    buscar: Función auxiliar que busca el valor de una variable en una interpretación dada.
    La función toma una variable (String) y una interpretación (lista de pares) y devuelve 
        el valor booleano asociado a esa variable.
    Si la variable no se encuentra en la interpretación, devuelve False por defecto.
-}
buscar :: String -> Interpretacion -> Bool
buscar x [] = False
buscar x ((y,v):xs)
    | x == y    = v
    | otherwise = buscar x xs

{-
    eval: Función que evalúa una fórmula bajo una interpretación dada.
    La función toma una interpretación y una fórmula y devuelve el valor booleano resultante.
-}
eval :: Interpretacion -> LProp -> Bool
eval i (Var x) = buscar x i
eval i (Not p) = not (eval i p)
eval i (And p q) = eval i p && eval i q
eval i (Or p q) = eval i p || eval i q
eval i (Imp p q) = not (eval i p) || eval i q

{-
    vars: Función que devuelve una lista de todas las variables en una fórmula dada.
    Recorre la estructura de la fórmula y acumula las variables encontradas en una lista.
-}
vars :: LProp -> [String]
vars (Var x) = [x]
vars (Not p) = vars p
vars (And p q) = vars p ++ vars q
vars (Or p q) = vars p ++ vars q
vars (Imp p q) = vars p ++ vars q

{-
    varUnicas: Función que devuelve una lista de variables únicas en una fórmula dada.
    La función utiliza la función auxiliar varAux para eliminar duplicados.
-}
varUnicas :: LProp -> [String]
varUnicas p = varAux (vars p)

{-
    varAux: Función auxiliar que elimina duplicados de una lista de variables.
    Recorre la lista de variables y construye una nueva lista que contiene solo las variables únicas.
-}
varAux :: [String] -> [String]
varAux [] = []
varAux (x:xs) = x:(varAux (elimina x xs))

{-
    elimina: Función auxiliar que elimina todas las ocurrencias de un elemento en una lista.
    Toma un elemento y una lista, y devuelve una nueva lista sin ese elemento.
-}
elimina :: String -> [String] -> [String]
elimina x [] = []
elimina x (y:ys)
    | x == y    = elimina x ys
    | otherwise = y:(elimina x ys)

{-
    booleanos: Función que genera todas las combinaciones posibles de valores booleanos para n variables.
    Utiliza recursión para construir las combinaciones, agregando True y False a cada combinación generada 
        para n-1 variables.
-}
booleanos :: Int -> [[Bool]]
booleanos 0 = [[]]
booleanos n = [b:bs | b <- [True, False], bs <- booleanos (n-1)]

{-
    interpretaciones: Función que genera todas las interpretaciones posibles para una fórmula dada.
    La función utiliza las funciones auxiliares varUnicas y booleanos para construir las interpretaciones.
-}
interpretaciones :: LProp -> [Interpretacion]
interpretaciones p =
    let vs = varUnicas p
        bs = booleanos (length vs)
    in asignar vs bs

{-
    asignar: Función auxiliar que asigna valores booleanos a variables para generar interpretaciones.
    Toma una lista de variables y una lista de combinaciones de valores booleanos, y devuelve una lista de interpretaciones
        donde cada interpretación es una lista de pares (variable, valor).
-}
asignar :: [String] -> [[Bool]] -> [Interpretacion]
asignar vs [] = []
asignar vs (b:bs) = (zip vs b) : (asignar vs bs)

-- 4.2 Tabla de Verdad

{-
    tabla: Función que genera la tabla de verdad para una fórmula dada.
    La función utiliza la función interpretaciones para obtener todas las interpretaciones posibles, 
        y luego evalúa la fórmula bajo cada interpretación para construir la tabla de verdad como una
        lista de pares (interpretación, valor).
-}
tabla :: LProp -> [(Interpretacion, Bool)]
tabla p = construirTabla (interpretaciones p) p

{-
    construirTabla: Función auxiliar que construye la tabla de verdad a partir de una lista de interpretaciones y una fórmula.
    Toma una lista de interpretaciones y una fórmula, y devuelve una lista de pares (interpretación, valor) donde el valor es el resultado
        de evaluar la fórmula bajo esa interpretación.
-}
construirTabla :: [Interpretacion] -> LProp -> [(Interpretacion, Bool)]
construirTabla [] _ = []
construirTabla (i:is) p = (i, eval i p) : construirTabla is p

-- 4.3 Propiedades Semanticas

{-
    esTautologia: Función que verifica si una fórmula es una tautología.
    Utiliza la función interpretaciones para obtener todas las interpretaciones posibles, y luego evalúa la fórmula bajo cada interpretación.
    Si la fórmula es verdadera en todas las interpretaciones, devuelve True, si no, devuelve False.
-}
esTautologia :: LProp -> Bool
esTautologia p = foldl (\acc x -> (eval x p) && acc) True (interpretaciones p)

{-
    esSatisfacible: Función que verifica si una fórmula es satisfacible.
    Utiliza la función interpretaciones para obtener todas las interpretaciones posibles, y luego evalúa la fórmula bajo cada interpretación.
    Si la fórmula es verdadera en al menos una interpretación, devuelve True, si no, devuelve False.
-}
esSatisfacible :: LProp -> Bool
esSatisfacible p = foldl (\acc x -> (eval x p) || acc) False (interpretaciones p)

{-
    esContradiccion: Función que verifica si una fórmula es una contradicción.
    Utilizamos la función esSatisfacible y la negación de su resultado para determinar si la fórmula es una contradicción.
    Si la fórmula no es satisfacible, entonces es una contradicción, por lo que devolvemos True.
-}
esContradiccion :: LProp -> Bool
esContradiccion p = not (esSatisfacible p)

-- 4.4 Lenguaje Proposicional Mínimo - Definición de nuevo tipo algebraico y función aMin


{-
    LPropMin: Nuevo tipo algebraico que representa fórmulas proposicionales utilizando solo los conectivos Not, And, Or.
    La función aMin toma una fórmula de tipo LProp y la convierte a una fórmula equivalente de tipo LPropMin utilizando solo los conectivos permitidos.
-}
data LPropMin = VarMin String
                | NotMin LPropMin
                | AndMin LPropMin LPropMin
                | OrMin LPropMin LPropMin
                deriving (Show, Eq)

{-
    aMin: Función que convierte una fórmula de tipo LProp a una fórmula equivalente de tipo LPropMin.
    La función recorre la estructura de la fórmula original y construye una nueva fórmula utilizando solo los conectivos Not, And, Or.
    Para el caso del conectivo Imp, se utiliza la equivalencia p → q ≡ ¬p ∨ q para convertirlo a una fórmula sin implicación.
-}
aMin :: LProp -> LPropMin
aMin (Var x) = VarMin x
aMin (Not p) = NotMin (aMin p)
aMin (And p q) = AndMin (aMin p) (aMin q)
aMin (Or p q) = OrMin (aMin p) (aMin q)
aMin (Imp p q) = OrMin (NotMin (aMin p)) (aMin q)