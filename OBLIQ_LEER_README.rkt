#|
Proyecto final de FLP entregado por los siguientes estudiantes:
Juan David Camacho 2266292
Wilson Andres Martinez 2266319
Juan Gabriel Paredes 2266183
||#

#lang eopl

#|
<programa>                       ::= <expresion>
<expresion>                      ::= <bool-expresion>
                                 ::= <identificador>
                                 ::= <numero>
                                 ::= <caracter>
                                 ::= <cadena>
                                 ::= ok  
                                 ::= var {<identificador> = <expresioni>}*(,) in <expresion> end
                                 ::= let {<identificador> = <expresioni>}*(,) in <expresion> end
                                 ::= letrec {<identificador> ({<identificadori>}*(,)) = <expresion>}* in <expresion> end
                                 ::= set <identificador> := <expresion>
                                 ::= begin <expresion> {<expresion>}*(;) end
                                 ::= <primitiva> ({<expresion>}*)
                                 ::= if <bool-expresion> then <expresion> {elseif <bool-expresion> then <expresion>}* else <expresion> end
                                 ::= proc ({<identificador>}*(,)) <expresion> end
                                 ::= apply <identificador> ({<expresion>}*(,))
                                 ::= meth (<identificador>, {<identificador>}*(,)) <expresion> end
                                 ::= for <identificador> = <expresion> to <expresion> do <expresion> end
                                 ::= object {{<identificador> => <expresion>}*} end
                                 ::= get <identificador>.<identificador>
                                 ::= send <identificador>.<identificador>({<identificador>}*(,))
                                 ::= update <identificador>.<identificador> := <expresion>
                                 ::= clone (<identificador> {<identificador>}*(,))

<bool-expresion>                 ::= true
                                 ::= false
                                 ::= <bool-primitiva>({<expresion>}*)
                                 ::= <bool-oper>({<bool-expresion>}*)
                                                     
<primitiva>                      ::= + |- |* |/ | % | & 
<bool-primitiva>                 ::= < | > | <= | >= |is 
<bool-oper>                      ::= not |and |or 

|#
;Despues de haber sustentado corregimos el scaner  aumentando los number por comprencion a a la gramatica.
(define scanner-spec-simple-interpreter
  '((white-sp (whitespace) skip)
    (comment ("(*" (arbno (not #\newline)) "*)") skip)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (number (digit (arbno digit) "." digit (arbno digit)) number)
    (number ("-" digit (arbno digit) "." digit (arbno digit)) number)
    (identifier (letter (arbno (or letter digit "_" "$")))symbol)
    (char ("'" (or letter digit) "'") string)
    (string ("\"" (arbno (or letter digit whitespace)) "\"") string)))

;; Especificación de la gramática
(define grammar-simple-interpreter
  '(
    (program (expression) a-program)
    (expression (bool-expresion) bool-expresion-exp)
    (expression (identifier) ide-exp)
    (expression (number) num-exp)
    (expression (char) char-exp)
    (expression (string) string-exp)
    ;(expression ("true") bool-true-exp) se comenta esto porque no esta expuesto en el proyecto
    ;(expression ("false") bool-false-exp) Esto no iba pero se puso por guia de interpretadores
    (expression ("ok") ok-exp)
    ;se corrigen la expresiones para que funcione mejor el interprete no tenia ejecucion
    (expression ("var" (separated-list identifier "=" expression ",") "in" expression "end") var-exp)
    (expression ("let" (separated-list identifier "=" expression ",") "in" expression "end") let-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression "end") letrec-exp)
    (expression ("set" identifier ":=" expression) set-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression (primitive "(" (arbno expression) ")") primapp-exp)
    (expression ("if" bool-expresion "then" expression(arbno "elseif" bool-expresion "then" expression) "else" expression "end") if-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression ) proc-exp)
    (expression ("apply" identifier "(" (separated-list expression ",") ")") apply-exp)
    ;;(expression ("meth" "(" identifier "," (separated-list identifier ",") ")" expression "end") method-exp)
    (expression ("for" identifier "=" expression "to" expression "do" expression "end") for-exp)
    ;; Se expresan los dimas expresiones expuestas en el proyecto.
    ;; Expresiones booleanas
    (bool-expresion ("true") true-exp)
    (bool-expresion ("false") false-exp)
    (bool-expresion (bool-primitive "(" (separated-list expression ",") ")") bool-primitive-exp)
    (bool-expresion (bool-oper "(" (separated-list bool-expresion ",") ")") bool-oper-exp)

    (bool-primitive ("<") bool-menor-prim)
    (bool-primitive (">") bool-mayor-prim)
    (bool-primitive ("<=") bool-menorigual-prim)
    (bool-primitive (">=") bool-mayorigual-prim)
    (bool-primitive ("is") bool-is-prim)

    (bool-oper ("and") bool-and-oper)
    (bool-oper ("or") bool-or-oper)
    (bool-oper ("not") bool-not-oper)

    ;;Primitivas
    (primitive ("+") add-prim)
    (primitive ("-") subtract-prim)
    (primitive ("*") mult-prim)
    (primitive ("&") concat-prim)
    (primitive ("%") mod-prim)))

;; Funciones nuevas añadidas
;;(define show-the-datatypes
;;  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;;(define just-scan (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;; Crea tipo de datos (datatype)
(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

;; Análisis léxico y sintáctico integrados
(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;; Estas partes no se tenian anteriormente en el proyecto.
;; Se define el tipo de dato para los valores (datatype) y demas procedimientos
(define-datatype procesx procesx?
  (closure (ls (list-of symbol?))
  (body expression?)
  (ambi-created ambi?)))

;;Referencias
(define-datatype reference reference?
  (derf (pss number?) (vet vector?)))

(define dedef
  (lambda (der) (primitive-dedef der)))

(define primitive-dedef
  (lambda (der)
  (cases reference der
  (derf (pss vet)
  (vector-ref vet pss)))))

(define setref!
  (lambda (der varr)
  (primitive-setref! der varr)))

(define primitive-setref!
  (lambda (der varr)
  (cases reference der
  (derf (pss vet)
  (vector-set! vet pss varr)))))

;;Definiciones evaludores
(define eval-bool-primitive
  (lambda (bo-prim lvas)
  (cases bool-primitive bo-prim
    (bool-menor-prim () (apply < lvas))
    (bool-mayor-prim () (apply > lvas))
    (bool-menorigual-prim () (apply <= lvas))
    (bool-mayorigual-prim () (apply >= lvas))
    (bool-is-prim () (apply = lvas)))))

(define eval-prim-exp
  (lambda (prim lvalues)
    (cases primitive prim
      (add-prim () (apply + lvalues))
      (subtract-prim () (apply - lvalues))
      (mult-prim () (apply * lvalues))
      (concat-prim () (apply string-append lvalues))
      (mod-prim () (apply  modulo lvalues)))))

(define list-find-pos
  (lambda (sim lista)
    (letrec
      ((auxiliar
        (lambda (l pss)
          (cond
          [(null? l) (eopl:error "No se encontro el simbolo" sim)]
          [(equal? sim (car l)) pss]
          [else
          (auxiliar (cdr l) (+ pss 1))]))))
          (auxiliar lista 0))))

(define (and-map f l)
  (if (null? l) #t
    (if (f (car l))
      (and-map f (cdr l)) #f)))

(define (or-map f l)
  (if (null? l) #f
    (if (f (car l)) #t
      (or-map f (cdr l)))))

(define identifica (lambda (x) x))

(define eval-bool-oper
  (lambda (oper lvals)
    (cases bool-oper oper
    (bool-and-oper () (and-map identifica lvals))
    (bool-or-oper () (or-map identifica lvals))
    (bool-not-oper ()
    (if (= (length lvals) 1)
      (not ( car lvals))
      (eopl:error "Not solo espera un valor"))))))
      
;;Expresiones booleanas
(define eval-bool-expression
  (lambda (exp amb)
  (cases bool-expresion exp
    (true-exp () #t)
    (false-exp () #f)
    (bool-primitive-exp (bo-prim e)
      (let
        ((lvas (map (lambda (exp) (eval-expression exp amb)) e)))
        (eval-bool-primitive bo-prim lvas)))
    (bool-oper-exp (bool-oper e)
      (let
        ((lvas (map (lambda (exp) (eval-bool-expression exp amb)) e)))
         (eval-bool-oper bool-oper lvas))))))
#|
(define (apply-env env id)
  (cond
    ((null? env) (my-error (string-append "Unbound identifier: " (symbol->string id))))
    ((eq? id (car (car env))) (cdr (car env)))
    (else (apply-env (cdr env) id))))

;; Función auxiliar para evaluar expresiones
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-expression x env)) rands)))

;; Intérprete
(define eval-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (body)                        
        (eval-expression body (init-env))))))

;; Ambiente Inicial
(define init-env 
  (lambda ()
    empty-env))
|#

(define eval?
 (lambda (eval)
    #t))


#|
(define empty-env '())

(define (extend-env ids vals env)
  (if (null? ids)
      env
      (cons (cons (car ids) (car vals))
            (extend-env (cdr ids) (cdr vals) env))))
|#

;; Se corrige lo anterior ya que no se creo los propios ambientes para los entornos
;; Definicion de entornos
;;defino el ambiente
(define-datatype ambi ambi?
 (ambi-empty)
 (ambi-extend
  (lis (list-of symbol?))
  (lvalue (list-of eval?))
  (old-env ambi?))
  (ambi-extend-ant
    (procnames (list-of symbol?))
    (liss (list-of (list-of symbol?)))
    (bodys (list-of expression?))
    (old-env ambi?))
  (ambi-extend-der
    (lis (list-of symbol?))
    (lvalue vector?)
    (old-env ambi?)))

(define cont-env
  (lambda (amb var)
    (let
      ((der (apply-env amb var)))
      (if (reference? der)
      (dedef der)
      der))))

;; En vez de crear un ambiente vacio inicial bacio se le da un valor.
(define ambi-init
  (ambi-extend '(x y z) '(1 2 3) (ambi-empty)))

#|
;;  aplicar primitivas
(define apply-primitive
  (lambda (prim args)
    (cases primitive prim
      (add-prim  () (+ (car args)  (cadr args))) 
      (subtract-prim () (- (car args) (cadr args)))
      (mult-prim  () (* (car args) (cadr args)))
      (div-prim  () (/ (car args) (cadr args)))
      (mod-prim  () (modulo (car args) (cadr args))))))
|#

;; En este caso se aplica bien el apply con sentido al proyecto.
(define apply-env
  (lambda (env var)
  (cases ambi env
  (ambi-empty () (eopl:error "No has puesto ningun variable" var))
  (ambi-extend (ls lval old-env)
  (letrec
    ((look-variable
    (lambda (ls lval)
    (cond
    [(null? ls) (apply-env old-env var)]
    [(equal? (car ls) var) (car lval)]
    [else
    (look-variable (cdr ls) (cdr lval))]))))
    (look-variable ls lval)))
    (ambi-extend-ant (procnames liss bodys old-env)
      (let
        ((pss (list-find-pos var procnames)))
        (if (number? pss)
        (closure
        (list-ref liss pss)
        (list-ref bodys pss) env)
        (apply-env old-env var))))
        (ambi-extend-der (ls vet old-env)
          (letrec
            ((look-variable
            (lambda (ls vet pss)
            (cond
            [(null? ls) (apply-env old-env var)]
            [(equal? (car ls) var) (derf pss vet)]
            [else
            (look-variable (cdr ls) vet (+ pss 1))]))))
            (look-variable ls vet 0))))))


(define set-env!
  (lambda (env var varr)
  (cases ambi env
  (ambi-empty () (eopl:error "No has puesto ningun variable" var))
  (ambi-extend (lis lvalues old-env)
  (letrec
    ((look-variable 
    (lambda (lis lvalues)
    (cond
    [(null? lis) (set-env! old-env var varr)]
    [(equal? (car lis) var) (eopl:error "No puedes cambiar el valor de una variable" var)]
    [else
    (look-variable (cdr lis) (cdr lvalues))]))))
    (look-variable lis lvalues)))
    (ambi-extend-ant (procnames liss bodys old-env)
      (letrec
        ((look-variable
        (lambda (procnames)
        (cond
        [(null? procnames) (set-env! old-env var varr)]
        [(equal? (car procnames) var) (eopl:error "No puedes cambiar el valor de una variable" var)]
        [else
        (look-variable (cdr procnames))]))))
        (look-variable procnames)))
        (ambi-extend-der (lis vet old-env)
        (setref! (apply-env env var) varr)))))
  
#|
Se corrige este eval-expression
;; Evaluador de expresiones
(define eval-expression 
  (lambda (exp env)
    (cases expression exp
      (var-exp (id) 
        (apply-env env id))
      (lit-exp (datum) 
        datum)     
      (char-exp (char) 
        char) 
      (string-exp (string) 
        string)
      (bool-true-exp () 
        'true)
      (bool-false-exp () 
        'false) 
      (ok-exp () 
        'ok)
      (vari-exp (ids rands body)
        (let ((args (eval-rands rands env)))
          (eval-expression body (extend-env ids args env))))
      (let-exp (ids rands body)
        (let ((args (eval-rands rands env)))
          (eval-expression body (extend-env ids args env))))
      (set-exp (id rhs-exp)  
        (begin
          (set! (apply-env env id) (eval-expression rhs-exp env))
          1))           
      (begin-exp (exp1 exp2)
        (let ((acc (eval-expression exp1 env))
              (exp2 exp2))
          (if (null? exp2) 
              acc
              (eval-expression exp2 env))))       
      (primapp-exp (prim rands)              
        (let ((args (eval-rands rands env))) 
          (apply-primitive prim args)))
      (if-exp (test-exp then-exp else-exps then-exps else-exp)
        (if (eval-expression test-exp env)
            (eval-expression then-exp env)
            (eval-expression else-exp env)))
      (proc-exp (ids body) 
        (lambda (args)
          (eval-expression body (extend-env ids args env))))
      (apply-exp (rator rands)
        (let ((proc (eval-expression rator env))
              (args (eval-rands rands env)))
          (proc args)))
      (for-exp (id start-exp end-exp body)
        (let loop ((i (eval-expression start-exp env))
                  (end (eval-expression end-exp env)))
          (if (> i end)
              'ok
              (begin
                (eval-expression body (extend-env (list id) (list i) env))
                (loop (+ i 1) end)))))
      (else (my-error (string-append "Unknown expression type: " (format "~a" exp)))))))
|#

;;Definimos extructuras
(define eval-expression
  (lambda (exp amb)
  (cases expression exp
    (bool-expresion-exp (bool-exp) (eval-bool-expression bool-exp amb))
    (num-exp (num) num)
    (ide-exp (ide) (cont-env amb ide))
    (char-exp (charr) (string-ref charr))
    (string-exp (str) (substring str 1 (- (string-length str) 1)))
    (ok-exp () empty)
    ;;var
    (var-exp (lis lexx body)
      (let
        ((lvalues (map (lambda (x) (eval-expression x amb )) lexx)))
        (eval-expression body (ambi-extend-der lis (list->vector lvalues) amb))))
    ;;let
    (let-exp (lis lexx body)
      (let
        ((lvalues (map (lambda (x) (eval-expression x amb )) lexx)))
        (eval-expression body (ambi-extend lis lvalues amb))))
    ;;letrec
    (letrec-exp (procnames idss bodys bo-letrec)
    (eval-expression bo-letrec (ambi-extend-ant procnames idss bodys amb)))
    ;;set
    (set-exp (var exp)
      (let
        ((varr (eval-expression exp amb)))
        (set-env! amb var varr)))
    ;;begin
    (begin-exp (exp lex)
      (if (null? lex)
          (eval-expression exp amb)
          (begin
            (eval-expression exp amb)
            (letrec
              ((eval-begin
              (lambda (lex)
                (cond
                [(null? (cdr lex)) (eval-expression (car lex) amb)]
                [else
                (begin (eval-expression (car lex) amb)
                       (eval-begin (cdr lex)))]))))
                       (eval-begin lex)))))
     ;;primitiva
    (primapp-exp (prim lex)
      (let
        ((lvalues (map (lambda (x) (eval-expression x amb)) lex)))
        (eval-prim-exp prim lvalues)))
    ;;if
    (if-exp (con is-true lli lexx is-false)
      (cond
      [(eval-bool-expression con amb) (eval-expression is-true amb)]
      [(null? lli) (eval-expression is-false amb)]
      [else
      (eval-expression (if-exp (car lli) (car lexx) (cdr lli) (car lexx) is-false) amb)]))
    ;;proc
    (proc-exp (ids body) (closure ids body amb))
    ;;apply
    (apply-exp (procname lexx)
      (let
        ((rr (map (lambda (x) (eval-expression x amb)) lexx))
        (proces (cont-env amb procname)))
        (if (procesx? proces)
          (cases procesx proces
          (closure (lit body old-env)
          (if (= (length lit) (length rr))
            (eval-expression body (ambi-extend-der lit (list->vector rr) old-env))
            (eopl:error "argumento incorrecto, -->" (length lit) "argumento enviado" (length rr)))))
            (eopl:error "No es un procedimiento" proces))))
    ;;for
    (for-exp (cd valu cond-s va)
      (letrec
        ((lvalues (list (eval-expression valu amb)))
         (condi (eval-expression cond-s amb))
         (cdd (ambi-extend-der (list cd) (list->vector lvalues) amb))
         (itera
         (lambda (cdd varr condi va)
          (let*
            ([n-amb (ambi-extend-der (list cd) (list->vector varr) amb)]
             [result-va (eval-expression va n-amb)]
             [n-varr (+ 1 (car varr))])
             (if (> n-varr condi) result-va
             (itera cdd (list n-varr) condi va))))))
             (itera cdd lvalues condi va))))))

;;Evaluar programa
(define eval-program
  (lambda (pgm)
  (cases program pgm
  (a-program (exp)
  (eval-expression exp ambi-init)))))

;; Se define el interprete
(define interpretador
  (sllgen:make-rep-loop "-->"
    (lambda (pgm) (eval-program pgm))
    (sllgen:make-stream-parser
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

(provide (all-defined-out))
(interpretador)

;; (interpretador "let x = 5 in let y = 3 in x + y) end")
