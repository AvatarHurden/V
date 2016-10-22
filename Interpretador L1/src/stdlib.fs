﻿module stdlib

let content = """

// ====================
// Arithmetic functions
// ====================

let rec remainder(x, y) {
    if y = 0 then  
        raise
    else if x<y then
        x
    else
        remainder (x-y) y
};

let negate(x) {
	0-x
};

let abs(x) {
	if x < 0 then
		negate x
	else
		x
};

// =================
// Logical functions
// =================

let not(t) {
	if t then
		false
	else
		true
};

let and(t1, t2) {
	if t1 then
		t2
	else
		false
};

let or(t1, t2) {
	if t1 then
		true
	else
		t2
};

let xor(t1, t2) {
	if t1 then
		not t2
	else
		t2
};

// ====================
// Basic List functions
// ====================

let rec append(x, ls) {
	if empty? ls then
		x::ls
	else
		(head ls)::(append x (tail ls))
};

let rec concat(ls1, ls2) {
	if empty? ls1 then
		ls2
	else
		(head ls1)::(concat (tail ls1) ls2)
};

let rec last(ls) {
	if empty? ls then
		raise
	else if empty? (tail ls) then
		head ls
	else
		last (tail ls)
};
let rec init(ls){
	if empty? ls then
		raise
	else if empty? (tail ls) then
		nil
	else
		(head ls)::(init (tail ls))
};
let rec length(ls) {
	if empty? ls then
		0
	else
		1 + length (tail ls)
};


// =========================
// List generation functions
// =========================

let rec range(start, finish, inc) {
	if ((start > finish && inc > 0) || (start < finish && inc < 0)) then
		nil
	else if (inc > 0 && start <= finish) || (inc < 0 && start >= finish) then
		start::(range (start+inc) finish inc)
	else
		nil
};

// =============================
// List transformation functions
// =============================

let reverse(ls) {
	if empty? ls then
		nil
	else
		let rec f(lsOld, lsNew) {
			let new = (head lsOld)::(lsNew);
			if empty? (tail lsOld) then
				new
			else
				f (tail lsOld) new
		};
		f ls nil
};

let rec map(f, ls) {
    if empty? ls then
        nil
    else
        (f (head ls))::(map f (tail ls))
};


// ========================
// List reduction functions
// ========================

let rec fold(f, acc, ls) {
    if empty? ls then
        acc
    else
        fold f (f acc (head ls)) (tail ls)
};

let rec reduce(f, ls) {
    if empty? ls then
        raise
    else if empty? (tail ls) then
        head ls
    else
        f (head ls) (reduce f (tail ls))
};

let rec all(pred, ls) {
	if empty? ls then
		true
	else if (head ls) |> pred |> not then
		false
	else
		(tail ls) |> all pred
};

let rec any(pred, ls) {
	if empty? ls then
		false
	else if (head ls) |> pred then
		true
	else
		(tail ls) |> any pred
};

let maximum(ls) {
    reduce (\acc, x => if acc < x then x else acc) ls
};

let minimum(ls) {
    reduce (\acc, x => if acc > x then x else acc) ls
};

// =================
// Sublist functions
// =================

let rec take(x, ls) {
	if (x = 0) || (empty? ls) then
		nil
	else
		(head ls)::((tail ls) |> take (x-1))
};

let rec drop(x, ls) {
    if x > 0 && empty? ls then
        []
    else if x = 0 then
        ls
    else
        drop (x-1) (tail ls)
};

let rec takeWhile(pred, ls) {
	if empty? ls then
		nil
	else if (head ls) |> pred |> not then
		nil
	else
		(head ls)::(tail ls |> takeWhile pred)
};

let rec dropWhile(pred, ls) {
    if empty? ls then
        []
    else if head ls |> pred |> not then
        ls
    else
        dropWhile pred (tail ls)
};

let subList(start, end, ls) {
    if start < 0 || end < 0 || end < start || end > length ls then
        raise
    else
        take (end-start) <| drop start ls 
};

// =====================
// List search functions
// =====================

let rec exists(t, ls) {
    if empty? ls then
        false
    else if t = (head ls) then
        true
    else
        exists t <| tail ls
};      

let rec filter(pred, ls) {
	if empty? ls then
		nil
	else if head ls |> pred then
		head ls::tail ls |> filter pred
	else
		tail ls |> filter pred
};

// =======================
// List indexing functions
// =======================

let indexOf(t, ls) {
    let rec f(index, ls) {
	    if empty? ls then
		    -1
	    else if t = (head ls) then
		    index
        else
            f (index+1) (tail ls)
	};
    f 0 ls
};

let rec nth(index, ls) {
    if index > 0 && empty? ls then 
        raise
    else if index = 0 then
        head ls
    else
        nth (index - 1) (tail ls)
};

// ======================
// List sorting functions
// ======================

let rec sort(ls) {
    if empty? ls then
        []
    else
        let min = minimum ls;
        let index = indexOf min ls;
        let rest = take index ls @ (drop (index+1) ls);
        min::(sort rest)
};


"""