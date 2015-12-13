(*Zadanie: iSet*)
(*Autor: Paweł Zięcik*)
(*Recenzent: Artur Jamro*)

(*Reprezentacja: Node(l, x, y, r, h, n)
  [x, y] - przedzial (x <= y), h - wysokosc
  n - liczba elementow mniejszych od y w drzewie 
  l, r - odpowiedznio lewe, prawe drzewo*)

type t = Empty | Node of t * int * int * t * int * int  

let empty = Empty

let is_empty l = l = Empty 

let height = function
  | Empty -> 0
  | Node (_, _, _, _, h, _) -> h

let size = function
  | Empty -> 0
  | Node(_, _, _, _, _, n) -> n

let addNumber a b = (*Zwraca min max_int (a+b) (a >= 0 b >= 0*)
  if a <= a + b then a + b else max_int 

let len x y = max (y - x + 1) 0

let make l x y r =
    Node(l, x, y, r, max (height l) (height r) + 1, 
    addNumber (size l) (len x y))

let bal l x y r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lx, ly, lr, _, _) ->
      if height ll >= height lr 
        then make ll lx ly (make lr x y r)
        else
          (match lr with
          | Node (lrl, lrx, lry, lrr, _, _) ->
            make (make ll lx ly lrl) lrx lry (make lrr x y r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rx, ry, rr, _, _) ->
      if height rr >= height rl 
        then make (make l x y rl) rx ry rr
        else
          (match rl with
          | Node (rll, rlx, rly, rlr, _, _) ->
            make (make l x y rll) rlx rly (make rlr rx ry rr) 
          | Empty -> assert false)
    | Empty -> assert false
  else Node(l, x, y, r, max hl hr + 1,
    addNumber (size l) (len x y))

let rec addOneRight a t = (*Znajduje przedział ktorego koniec == a*) 
  match t with            (*i usuwa go z drzewa*)
  | Empty -> (Empty, (a + 1))   (*Przedzialu nie znaleziono*)
  | Node(l, x, y, r, _, _) -> (*Zakladamy y <= a rowniez dla kazdego*)
    if y = a                  (*przedzialu w poddrzewach*) 
      then (l, x)
      else
        let rt, lend = addOneRight a r in
        (bal l x y rt, lend)

let rec addOneLeft b t = (*Znajduje przedzial ktorego poczatek == b*)
  match t with           (*i usuwa go z drzewa*)
  | Empty -> (Empty, (b - 1))  (*Przedzialu nie znaleziono*)
  | Node(l, x, y, r, _, _) -> (*Zakladamy b <= x rowniez dla kazdego*)
    if x = b                  (*przedzialu w poddrzewach*)
      then (r, y)
      else
        let lt, rend = addOneLeft b r
        in
          (bal l x y lt, rend)

let rec addOne a b t = (*Zakladamy ze zostalo wykonane remove x y*) 
  match t with
  | Empty -> make Empty a b Empty
  | Node(l, x, y, r, _, _) ->
    if b + 1 < x 
      then bal (addOne a b l) x y r
      else if y + 1 < a
        then bal l x y (addOne a b r)
        else if y + 1 = a 
          then
            let rt, rend = addOneLeft (b + 1) r in
              bal l x rend rt
          else
            let lt, lend = addOneRight (a - 1) l in
              bal lt lend y r 

let rec join l a b r = 
  match (l, r) with
  | (Empty, _) -> addOne a b r
  | (_, Empty) -> addOne a b l
  | (Node(ll, lx, ly, lr, lh, _), Node(rl, rx, ry, rr, rh, _)) ->
    if lh > rh + 2 then bal ll lx ly (join lr a b r) else
    if rh > lh + 2 then bal (join l a b rl) rx ry rr else
    make l a b r

let split v t =
  let rec loop = function
    | Empty ->
      (Empty, false, Empty)
    | Node (l, x, y, r, _, _) ->
      if v < x then
        let (ll, pres, rl) = loop l in (ll, pres, join rl x y r) else
      if y < v then
        let (lr, pres, rr) = loop r in (join l x y lr, pres, rr) else  
      let l = if x < v then addOne x (v - 1) l else l in
      let r = if y > v then addOne (v + 1) y r else r in 
        (l, true, r)      
  in loop t

let rec minElt = function
  | Node(Empty, x, y, _, _, _) -> x, y
  | Node(l, _, _, _, _ , _) -> minElt l
  | Empty -> raise Not_found

let rec removeMinElt = function
  | Node (Empty, _, _, r, _, _) -> r
  | Node (l, x, y, r, _, _) -> bal (removeMinElt l) x y r
  | Empty -> invalid_arg "ISet.remove_min_elt"

let merge t1 t2 = 
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
    let (x, y) = minElt t2 in
    bal t1 x y (removeMinElt t2)

let remove (x, y) t =
  let (l, _, _) = split x t in
  let (_, _, r) = split y t in
    merge l r

let add (a, b) t =
  let t = remove (a, b) t in
    addOne a b t

let rec mem v = function
  | Empty -> false
  | Node(l, x, y, r, _, _) ->
      if x <= v && v <= y 
        then true
        else if v < x 
          then mem v l
          else mem v r

let rec iter f = function
  | Empty -> ()
  | Node(l, x, y, r, _, _) ->
      iter f l; f (x, y);iter f r

let rec fold f t a =
  match t with
  | Empty -> a
  | Node(l, x, y, r, _, _) ->
    fold f r (f (x, y) (fold f l a))

let elements t =
  let rec loop t a =   
    match t with
    | Empty -> a
    | Node(l, x, y, r, _, _) -> loop l ((x, y)::(loop r a))
  in loop t []

let below v t =
  let rec loop t acc = 
    match t with
    | Empty -> acc
    | Node(l, x, y, r, _, n) ->
      if v > y
        then loop r (addNumber acc n)
        else loop l (addNumber acc (len x v)) 
  in loop t 0
