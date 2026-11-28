import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49902_aux

open PEqualNP.CircuitLowerBounds

private abbrev Col := Fin 5 → Bool

private def zeroCol : Col := fun _ => false
private def oneCol : Col := fun _ => true
private def bits (mask : Nat) : Col := fun t => mask.testBit t.val
private def meet (a b : Col) : Col := fun t => a t && b t
private def join (a b : Col) : Col := fun t => a t || b t
private def inv (a : Col) : Col := fun t => !a t

private def initial : List Col := [bits 30,bits 28,bits 24,bits 16,zeroCol,oneCol]
private def word (c : Col) : Nat :=
  (if c 0 then 1 else 0) + (if c 1 then 2 else 0) + (if c 2 then 4 else 0) +
    (if c 3 then 8 else 0) + (if c 4 then 16 else 0)

private theorem word_bit : ∀ (c : Col) (t : Fin 5), (word c).testBit t.val = c t := by
  decide +kernel

private theorem word_lt (c : Col) : word c < 2^5 := by
  have digit (b : Bool) (w : Nat) : (if b then w else 0) ≤ w := by cases b <;> simp
  have d0 := digit (c 0) 1
  have d1 := digit (c 1) 2
  have d2 := digit (c 2) 4
  have d3 := digit (c 3) 8
  have d4 := digit (c 4) 16
  unfold word
  omega

private theorem word_ext {a b : Nat} (smallA : a < 2^5) (smallB : b < 2^5)
    (lower : ∀ t : Fin 5, a.testBit t.val = b.testBit t.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases low : i < 5
  · exact lower ⟨i,low⟩
  · have enough : 2^5 ≤ (2 : Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (smallA.trans_le enough),Nat.testBit_lt_two_pow (smallB.trans_le enough)]

private theorem word_meet (a b : Col) : word (meet a b) = (word a &&& word b) := by
  apply word_ext (word_lt _) (Nat.and_lt_two_pow _ (word_lt _))
  intro t
  simp [meet,word_bit]

private theorem word_join (a b : Col) : word (join a b) = (word a ||| word b) := by
  apply word_ext (word_lt _) (Nat.or_lt_two_pow (word_lt _) (word_lt _))
  intro t
  simp [join,word_bit]

private theorem word_inv (a : Col) : word (inv a) = (word a ^^^ 31) := by
  apply word_ext (word_lt _) (Nat.xor_lt_two_pow (word_lt _) (by decide))
  intro t
  have high : ∀ t : Fin 5, (31 : Nat).testBit t.val = true := by decide +kernel
  simp [inv,word_bit,high]

private def binary (s : List Nat) : List Nat :=
  s.flatMap fun a => s.flatMap fun b => [a &&& b,a ||| b]

private def fresh (s xs : List Nat) : List Nat := xs.dedup.filter fun c => decide (c ∉ s)

private theorem mem_fresh {s xs : List Nat} {c : Nat} (hc : c ∈ xs) (hs : c ∉ s) :
    c ∈ fresh s xs := by simp [fresh,hc,hs]

private def deficit (s : List Nat) : Nat :=
  (if 4 ∈ s then 0 else 1) + (if 6 ∈ s then 0 else 1) + (if 21 ∈ s then 0 else 1)

private theorem deficit_add (s : List Nat) (c : Nat) : deficit s ≤ deficit (c :: s) + 1 := by
  by_cases h4 : 4 = c
  · subst c
    by_cases h : 4 ∈ s
    · simp [deficit,h]
    · simp [deficit,h]
      omega
  by_cases h6 : 6 = c
  · subst c
    by_cases h : 6 ∈ s
    · simp [deficit,h]
    · simp [deficit,h]
      omega
  by_cases h21 : 21 = c
  · subst c
    by_cases h : 21 ∈ s <;> simp [deficit,h]
  simp [deficit,h4,h6,h21]

private def binaryPossible (s : List Nat) (c : Nat) : Bool :=
  s.any fun a => s.any fun b => (a &&& b == c) || (a ||| b == c)

private def unaryPossible (s : List Nat) (c : Nat) : Bool :=
  s.any fun a => a ^^^ 31 == c

private theorem binary_possible {s : List Nat} {c : Nat} (mem : c ∈ binary s) :
    binaryPossible s c = true := by
  obtain ⟨a,ha,subs⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp subs
  refine List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl <;> simp

private theorem unary_possible {s : List Nat} {c : Nat} (mem : c ∈ s.map (fun a => a ^^^ 31)) :
    unaryPossible s c = true := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
  exact List.any_eq_true.mpr ⟨a,ha,by simp⟩

private def candidates (d : Nat) (s pool : List Nat) (possible : Nat → Bool) : List Nat :=
  if deficit s = d+1 then
    [4,6,21].filter fun c => decide (c ∉ s) && possible c
  else fresh s pool

private theorem candidate_mem (d : Nat) (s pool : List Nat) (possible : Nat → Bool) (c : Nat)
    (derived : c ∈ pool) (absent : c ∉ s) (valid : possible c = true)
    (room : deficit (c :: s) ≤ d) : c ∈ candidates d s pool possible := by
  by_cases tight : deficit s = d+1
  · have goal : c = 4 ∨ c = 6 ∨ c = 21 := by
      by_contra! other
      have same : deficit (c :: s) = deficit s := by
        simp [deficit,Ne.symm other.1,Ne.symm other.2.1,Ne.symm other.2.2]
      omega
    simpa [candidates,tight,absent,valid] using goal
  · simpa [candidates,tight] using mem_fresh derived absent

private def can : Nat → Nat → List Nat → Bool
  | 0, _, s => decide (4 ∈ s ∧ 6 ∈ s ∧ 21 ∈ s)
  | d+1, k, s =>
    if deficit s ≤ d+1 then
      can d k s ||
      ((candidates d s (binary s) (binaryPossible s)).any fun c => can d k (c :: s)) ||
      (if k = 0 then false else
        ((candidates d s (s.map fun c => c ^^^ 31) (unaryPossible s)).any fun c => can d (k-1) (c :: s)))
    else false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seed_denied : can 5 2 (initial.map word) = false := by
  decide +kernel

private def gateCol (w : List Col) (g : Gate) : Col :=
  fun t => g.op.eval (g.inputs.map fun i => w.getD i zeroCol t)

private def step (w : List Col) (g : Gate) : List Col := w ++ [gateCol w g]

private def rowInput (t : Fin 5) : List Bool :=
  (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]

private theorem initial_row : ∀ t : Fin 5, initial.map (fun c => c t) = rowInput t := by
  decide +kernel

private theorem lookup_row (w : List Col) (i : Nat) (t : Fin 5) :
    (w.map fun c => c t).getD i false = w.getD i zeroCol t := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem mapped_fold (gs : List Gate) (w : List Col) (t : Fin 5) :
    (gs.foldl step w).map (fun c => c t) =
      gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
        (w.map fun c => c t) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,step,List.map_append,List.map_cons,List.map_nil]
    simp only [gateCol,lookup_row]

private theorem lookup_mem {w : List Col} {s : List Nat}
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s) (i : Nat) : word (w.getD i zeroCol) ∈ s := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hasZero
  | some c => exact basis c (List.mem_of_getElem? h)

private theorem monotone_column (s : List Nat) (w : List Col) (g : Gate)
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s) (hasOne : word oneCol ∈ s)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    word (gateCol w g) ∈ s ∨ word (gateCol w g) ∈ binary s := by
  rcases h : g.inputs with _ | ⟨a,_ | ⟨b,tail⟩⟩
  · left
    rcases op with op | op
    · have eq : gateCol w g = oneCol := by funext t; simp [gateCol,h,op,GateOp.eval,oneCol]
      exact eq.symm ▸ hasOne
    · have eq : gateCol w g = zeroCol := by funext t; simp [gateCol,h,op,GateOp.eval,zeroCol]
      exact eq.symm ▸ hasZero
  · left
    have eq : gateCol w g = w.getD a zeroCol := by
      funext t
      rcases op with op | op <;> simp [gateCol,h,op,GateOp.eval]
    exact eq.symm ▸ lookup_mem basis hasZero a
  · have e : tail = [] := by simpa [h] using arity
    subst tail
    right
    unfold binary
    refine List.mem_flatMap.mpr ⟨word (w.getD a zeroCol),lookup_mem basis hasZero a,?_⟩
    refine List.mem_flatMap.mpr ⟨word (w.getD b zeroCol),lookup_mem basis hasZero b,?_⟩
    rcases op with op | op
    · have eq : gateCol w g = meet (w.getD a zeroCol) (w.getD b zeroCol) := by
        funext t
        simp [gateCol,h,op,GateOp.eval,meet]
      simp [eq,word_meet]
    · have eq : gateCol w g = join (w.getD a zeroCol) (w.getD b zeroCol) := by
        funext t
        simp [gateCol,h,op,GateOp.eval,join]
      simp [eq,word_join]

private theorem not_column (s : List Nat) (w : List Col) (g : Gate)
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s) (hasOne : word oneCol ∈ s)
    (op : g.op = .not) : word (gateCol w g) ∈ s ∨ word (gateCol w g) ∈ s.map (fun c => c ^^^ 31) := by
  cases h : g.inputs with
  | nil =>
    left
    have eq : gateCol w g = oneCol := by funext t; simp [gateCol,h,op,GateOp.eval,oneCol]
    exact eq.symm ▸ hasOne
  | cons a tail =>
    right
    have eq : gateCol w g = inv (w.getD a zeroCol) := by
      funext t
      simp [gateCol,h,op,GateOp.eval,inv]
    exact List.mem_map.mpr ⟨_,lookup_mem basis hasZero a,(word_inv _).symm.trans (congrArg word eq.symm)⟩

private def legal (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def switches (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs,0⟩

private theorem switches_cons_not (g : Gate) (gs : List Gate) (op : g.op = .not) :
    switches (g :: gs) = switches gs + 1 := by
  simp [switches,PEqualNP.NotBracket.notCount,op]

private theorem switches_cons_other (g : Gate) (gs : List Gate) (op : g.op ≠ .not) :
    switches (g :: gs) = switches gs := by
  simp [switches,PEqualNP.NotBracket.notCount,op]

private def hasOutputs (w : List Col) : Prop :=
  (∃ i, w.getD i zeroCol = bits 4) ∧ (∃ i, w.getD i zeroCol = bits 6) ∧
  (∃ i, w.getD i zeroCol = bits 21)

private theorem hasOutputs_in {w : List Col} {s : List Nat}
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s) (outputs : hasOutputs w) :
    4 ∈ s ∧ 6 ∈ s ∧ 21 ∈ s := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩⟩ := outputs
  have h4 := lookup_mem basis hasZero i
  have h6 := lookup_mem basis hasZero j
  have h21 := lookup_mem basis hasZero k
  rw [hi] at h4
  rw [hj] at h6
  rw [hk] at h21
  exact ⟨h4,h6,h21⟩

private theorem covers_step {w : List Col} {s : List Nat} {g : Gate}
    (basis : ∀ c ∈ w, word c ∈ s) (gate : word (gateCol w g) ∈ s) : ∀ c ∈ step w g, word c ∈ s := by
  intro c hc
  rcases List.mem_append.mp hc with old | new
  · exact basis c old
  · simpa using (List.mem_singleton.mp new) ▸ gate

private theorem enough_gates (gs : List Gate) (w : List Col) (s : List Nat)
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s)
    (outputs : hasOutputs (gs.foldl step w)) : deficit s ≤ gs.length := by
  induction gs generalizing w s with
  | nil =>
    obtain ⟨h4,h6,h21⟩ := hasOutputs_in basis hasZero outputs
    simp [deficit,h4,h6,h21]
  | cons g gs ih =>
    let c := word (gateCol w g)
    have old (v) (hv : v ∈ w) : word v ∈ c :: s := List.mem_cons_of_mem _ (basis v hv)
    have next := ih (step w g) (c :: s) (covers_step old List.mem_cons_self)
      (List.mem_cons_of_mem _ hasZero) outputs
    exact (deficit_add s c).trans (Nat.add_le_add_right next 1)

private theorem search_sound (d k : Nat) (gs : List Gate) (w : List Col) (s : List Nat)
    (basis : ∀ c ∈ w, word c ∈ s) (hasZero : word zeroCol ∈ s) (hasOne : word oneCol ∈ s)
    (ok : legal gs) (size : gs.length ≤ d) (count : switches gs ≤ k)
    (outputs : hasOutputs (gs.foldl step w)) : can d k s = true := by
  induction d generalizing k gs w s with
  | zero =>
    have empty : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp size)
    subst gs
    exact decide_eq_true (hasOutputs_in basis hasZero outputs)
  | succ d ih =>
    have room := (enough_gates gs w s basis hasZero outputs).trans size
    cases gs with
    | nil =>
      have prior := ih k [] w s basis hasZero hasOne ok (by simp) count outputs
      simp [can,room,prior]
    | cons g tail =>
      let c := word (gateCol w g)
      have gl := ok g (by simp)
      have tl : legal tail := fun g hg => ok g (List.mem_cons_of_mem _ hg)
      have short : tail.length ≤ d := by simpa using size
      have tailOutputs : hasOutputs (tail.foldl step (step w g)) := outputs
      by_cases repeats : c ∈ s
      · have tailCount : switches tail ≤ k := by
          by_cases on : g.op = .not
          · rw [switches_cons_not g tail on] at count
            omega
          · simpa only [switches_cons_other g tail on] using count
        have prior := ih k tail _ s (covers_step basis repeats) hasZero hasOne tl short tailCount tailOutputs
        simp [can,room,prior]
      · have old (v) (mv : v ∈ w) : word v ∈ c :: s := List.mem_cons_of_mem _ (basis v mv)
        have safe := covers_step (g := g) old List.mem_cons_self
        have zs : word zeroCol ∈ c :: s := List.mem_cons_of_mem _ hasZero
        have os : word oneCol ∈ c :: s := List.mem_cons_of_mem _ hasOne
        have tailRoom := (enough_gates tail _ _ safe zs tailOutputs).trans short
        by_cases on : g.op = .not
        · have derived := (not_column s w g basis hasZero hasOne on).resolve_left repeats
          have tailCount : switches tail + 1 ≤ k := by simpa only [switches_cons_not g tail on] using count
          have positive : k ≠ 0 := by omega
          have prior := ih (k-1) tail _ _ safe zs os tl short (by omega) tailOutputs
          have found : ((candidates d s (s.map fun v => v ^^^ 31) (unaryPossible s)).any
              fun v => can d (k-1) (v :: s)) = true :=
            List.any_eq_true.mpr ⟨c,candidate_mem d s _ _ c derived repeats (unary_possible derived) tailRoom,prior⟩
          simp [can,room,positive,found]
        · have binaryOp : g.op = .and ∨ g.op = .or := gl.1.elim Or.inl
            (fun alt => alt.elim Or.inr fun hn => (on hn).elim)
          have derived := (monotone_column s w g basis hasZero hasOne binaryOp gl.2).resolve_left repeats
          have tailCount : switches tail ≤ k := by simpa only [switches_cons_other g tail on] using count
          have prior := ih k tail _ _ safe zs os tl short tailCount tailOutputs
          have found : ((candidates d s (binary s) (binaryPossible s)).any fun v => can d k (v :: s)) = true :=
            List.any_eq_true.mpr ⟨c,candidate_mem d s _ _ c derived repeats (binary_possible derived) tailRoom,prior⟩
          simp [can,room,found]

theorem denied (D : Circuit) (p q r : Fin (6+D.size))
    (fan : PEqualNP.MetaComplexity.FanInTwo D) (limit : PEqualNP.NotBracket.notCount D ≤ 2)
    (size : D.size ≤ 5)
    (out : ∀ t : Fin 5, let w := D.wires (rowInput t)
      w.getD p.val false = (4 : Nat).testBit t.val ∧
      w.getD q.val false = (6 : Nat).testBit t.val ∧
      w.getD r.val false = (21 : Nat).testBit t.val) : False := by
  let w := D.gates.foldl step initial
  have cohere (t : Fin 5) : w.map (fun c => c t) = D.wires (rowInput t) := by
    change (D.gates.foldl step initial).map (fun c => c t) = _
    rw [mapped_fold,initial_row]
    rfl
  have get (i : Nat) (m : Nat) (real : ∀ t, (D.wires (rowInput t)).getD i false = m.testBit t.val) :
      w.getD i zeroCol = bits m := by
    funext t
    rw [← lookup_row,cohere,real t]
    rfl
  have outputs : hasOutputs w :=
    ⟨⟨p.val,get _ 4 (fun t => (out t).1)⟩,⟨q.val,get _ 6 (fun t => (out t).2.1)⟩,
      ⟨r.val,get _ 21 (fun t => (out t).2.2)⟩⟩
  have ok : legal D.gates := by
    intro g hg
    obtain ⟨basis,arity⟩ := fan g hg
    exact ⟨by simpa using basis,arity⟩
  have canWitness := search_sound 5 2 D.gates initial (initial.map word)
    (fun _ h => List.mem_map_of_mem h) (by simp [initial]) (by simp [initial]) ok size limit outputs
  exact Bool.noConfusion (seed_denied.symm.trans canWitness)

end PEqualNP.Outside.L_meta_49902_aux

theorem PEqualNP.Outside.L_meta_49902 :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
      ∀ t : Fin 5,
        let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (4 : Nat).testBit t.val ∧
        w.getD q.val false = (6 : Nat).testBit t.val ∧
        w.getD r.val false = (21 : Nat).testBit t.val) := by
  rintro ⟨D,p,q,r,fan,_,limit,size,out⟩
  exact PEqualNP.Outside.L_meta_49902_aux.denied D p q r fan limit size out
