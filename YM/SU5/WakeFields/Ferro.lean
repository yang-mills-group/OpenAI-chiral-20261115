import YM.SU5.Thin.Avalanche.Shelter
--! positively-priced bills over list of Gaussian tangent variables, order explicit
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.WakeFields.Ferro
open Filter Function MeasureTheory Topology
variable {α γ : Type*} (D : α → α → ℂ)

-- Roster with lookback. meter bounds recursion, ignored after length.
def dropOne (F : List α → ℂ) (x : α) (M L : List α) : ℂ := match L with
 | [] => 0 | i::t => D x i * F (M++t)+ dropOne F x (M++[i]) t

def fees (m : ℕ) (L : List α) : ℂ := match L,m with
 | [], _ => 1
 | _::_,0 => 0
 | x::L,m+1 => dropOne D (fees m) x [] L
 termination_by m
@[simp] lemma fees_nil (m) : fees D m []=1:=by rw [fees]
@[simp] lemma dnil (F : List α → ℂ) (x M) : dropOne D F x M []=0:=by rw [dropOne]
lemma bills_cons (F : List α → ℂ) (x M i L) : dropOne D F x M (i::L) = D x i * F (M ++ L)+ dropOne D F x (M++[i]) L:=by rw [dropOne]

variable (E : α → α → ℂ) (M L : List α) (x : α)

lemma afoot (p:∀ i∈L,D x i=E x i)(f f':List α→ ℂ)
    (h:∀ N, List.Sublist N (M++L) → f N=f' N) : dropOne D f x M L=dropOne E f' x M L:=by
  induction L generalizing M with
  | nil => rw [dnil,dnil]
  | cons i L ih =>
    have ht : (M ++ [i]) ++ L=M ++ (i::L) := by rw [List.append_assoc,List.singleton_append]
    rw [bills_cons,bills_cons,p i List.mem_cons_self,h _ (?_),ih _ (fun i v=> p i (List.mem_cons_of_mem _ v)) (ht.symm ▸ h)]; exact (List.Sublist.cons i (List.Sublist.refl L)).append_left _

lemma room (a b:ℕ)(t:L.length≤a)(v:a ≤ b) : fees D a L=fees D b L:=by
  induction a generalizing b L with
  | zero=> obtain rfl : L=[]:= (by simpa using t); simp
  | succ a ih=>
    cases L with
    | nil=> simp
    | cons i L =>
      have h:L.length≤a:=Nat.le_of_succ_le_succ t
      cases b with
      | zero=> omega
      | succ b =>
        rw [fees,fees]; exact afoot D D [] L i (fun i _=> rfl) _ _ (fun i p=> ih i b (p.length_le.trans h) (Nat.le_of_succ_le_succ v))

-- cut-independent
abbrev ledger : ℂ:= fees D L.length L
lemma ledger_nil : ledger D []=1 := by simp [ledger]
lemma resetFees (t) (h:L.length≤t): ledger D L=fees D t L:= room D L _ _ le_rfl h
lemma audit : ledger D (x::L)=dropOne D (ledger D) x [] L:=by
  change fees D (L.length+1) (x::L)= _; rw [fees]
  exact afoot D D [] L x (fun i _=> rfl) _ _ (fun i p=> (resetFees D i _ p.length_le).symm)
variable {β : Type*} (V : Filter β) (H : β → α → α → ℂ)

lemma motions (Y : α → α → Prop) (a : ℕ) (hp:L.length ≤ a) (g:L.Pairwise Y)
    (hf:∀ i j, Y i j → Tendsto (fun n=> H n i j) V (𝓝 (D i j))) :
        Tendsto (fun n=> ledger (H n) L) V (𝓝 (ledger D L)) := by
  induction a generalizing L with
  | zero => obtain rfl : L=[] := (by simpa using hp); simp_rw [ledger_nil]; exact tendsto_const_nhds
  | succ a ih =>
    cases L with
    | nil => simp_rw [ledger_nil]; exact tendsto_const_nhds
    | cons i L =>
      have hL:L.length ≤ a:=Nat.le_of_succ_le_succ hp
      have X (M W:List α) (Q:L=M++W) :
          Tendsto (fun n=>dropOne (H n) (ledger (H n)) i M W) V (𝓝 (dropOne D (ledger D) i M W)):=by
        induction W generalizing M with
        | nil=> simp_rw [dnil]; exact tendsto_const_nhds
        | cons j W HX =>
          simp_rw [bills_cons]
          have hS: List.Sublist (M++W) L:=by rw [Q]; exact (List.Sublist.cons j (List.Sublist.refl _)).append_left _
          have ht := ih _ (hS.length_le.trans hL) ((List.pairwise_cons.mp g).2.sublist hS)
          exact ((hf i j ((List.pairwise_cons.mp g).1 _ (Q.symm ▸ List.mem_append_right _ List.mem_cons_self))).mul ht).add (HX _ (by rw [List.append_assoc,List.singleton_append,Q]))
      simp_rw [audit]; exact X [] L rfl

-- map and append bookkeeping
lemma faces (A:γ→γ→ℂ)(f:α→γ)(h:∀ i j, D i j=A (f i) (f j))(w:ℕ)(p:L.length≤w):
    ledger D L= ledger A (L.map f):=by
  induction w generalizing L with
  | zero=> obtain rfl:L=[]:= (by simpa using p); simp [ledger]
  | succ k ih=>
    cases L with
    | nil=>simp [ledger]
    | cons i L=>
      have X (M W:List α)(Q:L=M++W): dropOne D (ledger D) i M W = dropOne A (ledger A) (f i) (M.map f) (W.map f) := by
        induction W generalizing M with
        | nil=> rw [dnil,List.map_nil,dnil]
        | cons x v hv=>
          have hl: List.Sublist (M++v) L:=by rw [Q]; exact (List.Sublist.cons x (List.Sublist.refl _)).append_left _
          rw [bills_cons,List.map_cons,bills_cons,h,ih _ (hl.length_le.trans (Nat.le_of_succ_le_succ p)),hv _ (by rw [List.append_assoc,Q,List.singleton_append])]; simp
      rw [List.map_cons,audit,audit]; exact X [] L rfl

lemma distinct_earn (p:∀ i∈L,∀ j∈M,D i j=0)(w:ℕ)(t:L.length≤w) : ledger D (L++M)=ledger D L*ledger D M:=by
  induction w generalizing L with
  | zero=> obtain rfl : L=[]:= (by simpa using t); simp [ledger]
  | succ w H=>
    cases L with
    | nil=>simp [ledger]
    | cons i L =>
      have x(k:List α)(t:List.Sublist k L): ledger D (k++M)= ledger D k*ledger D M:= H k (fun j h=> p j (List.mem_cons_of_mem _ (t.mem h))) (t.length_le.trans (Nat.le_of_succ_le_succ (by assumption)))
      have q(h:List α)(L':List α)(p':∀ x∈h,D i x=0): dropOne D (ledger D) i L' h=0 := by
        induction h generalizing L' with|nil=>rw[dnil]|cons j h ih=> rw [bills_cons,p' _ List.mem_cons_self,zero_mul,ih _ (fun x k=>p' x (List.mem_cons_of_mem _ k)),add_zero]
      have X (Y W:List α)(h:L=Y++W): dropOne D (ledger D) i Y (W++M)= dropOne D (ledger D) i Y W * ledger D M:=by
        induction W generalizing Y with
        | nil=> rw [List.nil_append,dnil,zero_mul]; exact q M Y (p i List.mem_cons_self)
        | cons i' W ih=>
          rw [List.cons_append, bills_cons,bills_cons,←List.append_assoc,x (Y++W) ?_,ih _ (by rw [List.append_assoc,h,List.singleton_append])]; rotate_left; · rw [h]; exact (List.Sublist.cons i' (List.Sublist.refl _)).append_left _
          ring
      rw [List.cons_append,audit,audit]; exact X [] L rfl

-- homogeneity -- scale everyone (thus covariance squared)
lemma multiplier (g:ℂ) (w:ℕ)(t:L.length≤w) : ledger (fun i j=> g^2 * D i j) L =g^L.length * ledger D L:=by
  induction w generalizing L with
  | zero=> obtain rfl:L=[]:= (by simpa using t); simp [ledger]
  | succ w ih=>
    cases L with
    | nil=>simp [ledger]
    | cons i L=>
      let F:=fun i j=>g^2 *D i j
      have X (M W:List α)(Q:L=M++W): dropOne F (ledger F) i M W=g^(L.length+1)*dropOne D (ledger D) i M W:=by
        induction W generalizing M with
        | nil=>simp
        | cons j W h=>
          have hs : List.Sublist (M++W) L := by rw [Q]; exact (List.Sublist.cons j (List.Sublist.refl _)).append_left _
          rw [bills_cons,bills_cons,h _ (by rw [List.append_assoc,List.singleton_append,Q])]; unfold F; rw [ih _ (hs.length_le.trans (Nat.le_of_succ_le_succ t))]
          rw [show L.length+1=(M++W).length+2 by simp [Q]; ring,pow_add]; ring
      rw [audit,audit]; exact X [] L rfl

open ProbabilityTheory Regis.Resonance
variable {Q:Type*}[NormedAddCommGroup Q][InnerProductSpace ℝ Q][MeasurableSpace Q][BorelSpace Q][FiniteDimensional ℝ Q]
theorem truePrice (x:α→Q) (w:ℕ)(p:L.length≤w) : ledger (fun i j=>(↑(inner ℝ (x i) (x j)):ℂ)) L = (memo (L.map x):ℂ):=by
  induction w generalizing L with
  | zero=> obtain rfl:L=[]:= (by simpa using p); simp [ledger,memo,payday]
  | succ w ih=>
    cases L with
    | nil=> simp [ledger,memo,payday]
    | cons i L=>
      let D':= fun i j=>(↑(inner ℝ (x i) (x j)):ℂ)
      have X (M W: List α)(g:L=M++W) : dropOne D' (ledger D') i M W= ↑(roster (x i) (M.map x) (W.map x)):=by
        induction W generalizing M with
        | nil=> simp [roster]
        | cons j W h =>
          have hs : List.Sublist (M++W) L := by rw [g]; exact (List.Sublist.cons j (List.Sublist.refl _)).append_left _
          rw [bills_cons,h _ (by rw [g,List.append_assoc,List.singleton_append]), List.map_cons,roster]; unfold D'; rw [ih _ (hs.length_le.trans (Nat.le_of_succ_le_succ p))]; simp
      rw [List.map_cons,audit,gramStein]; exact X [] L rfl
#print axioms audit
#print axioms truePrice
#print axioms distinct_earn
#print axioms multiplier
#print axioms motions
#print axioms faces
end YM.WakeFields.Ferro
