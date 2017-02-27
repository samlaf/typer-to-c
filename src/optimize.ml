(* optimize.ml --- A dummy optimizer  *)

module EL = Elexp
module EN = Env
module M = Myers

(* Vous recevez:
 * - une expression `e` de type `elexp` (défini dans elexp.ml)
 * - un contexte `ctx` qui donne la valeur associée à chaque variable
 *   du contexte.  Le contexte est représenté par une sorte de liste
 *   à accès O(log N) implémentée dans le fichier myers.ml.
 *   Chaque élément de la liste est une paire qui contient le nom
 *   (si la variable a un nom), et la valeur de la variable.
 * Malgré que les variables soient immuables, la valeur d'une variable est
 * stockée dans une "ref cell" parce que c'est la façon la plus simple
 * de gérer les définitions récursives.
 *
 * Vous devez renvoyer une nouvelle expression de type `elexp` équivalente à
 * `e` et idéalement plus simple/efficace.  *)

let optimize (ctx : (string option * (EN.value_type ref)) M.myers)
             (e : EL.elexp)
    : EL.elexp
  = e
