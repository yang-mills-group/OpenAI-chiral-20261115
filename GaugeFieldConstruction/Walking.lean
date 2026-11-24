import GaugeFieldConstruction.Ungrave
/-! P4 excitation budget. No frequency truncation in basis defining CH weights. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 50000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Function NormedSpace Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I] {P E A B:Op I}{u:UNI I}
variable {J:Type*}{Y Z:Op I}{x:Ket I}{v w:Wave I}{b e d h D K C:ℝ}
lemma tollSafe : fitV (univ: Finset I) (basisKet (n:=I)) 1 :=by
 intro x; rw [one_mul,←basis_draw x]; exact le_of_eq (sum_congr rfl fun i _=>by rw [←inner_conj_symm, Complex.norm_conj])
abbrev Creduct (I:Type*) := Bool × I
def RootBay (i:Creduct I) := creed i.1 (basisKet i.2)
lemma warp_root (t:Valve P E A B)(h:IsStarProjection P)(i:Creduct I) : translateW P A B u b (RootBay i)=creed i.1 (acts (if i.1 then star (onePeak P B u b) else oneWarp P A u b) (basisKet i.2)):=by obtain ⟨i|i,y⟩:=i; exact elevate t h ..; exact descend t h ..
lemma warp_word (t:Valve P E A B)(h:IsStarProjection P) (w:J→FC I)(L:List J): translateW P A B u b (rollC w L)=rollC (fun j=> translateW P A B u b (w j)) L:=by induction L with| nil=> simp [rollC,nilW t h] | cons i L ih=>unfold rollC; rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,translate_prod t h]; unfold rollC at ih; rw [ih]
lemma creed_delta (v:Bool)(x y:Ket I): ‖creed v x-creed v y‖≤ ‖x-y‖:=by
 rw [show creed v x-creed v y=creed v (x-y) from sub_eq_of_eq_add (by rw [←creed_a v, sub_add_cancel])]; exact Flare.cost_pe ..
lemma pearl_walk (g:1≤K)(ds:0≤d)(a:J→Bool)(X Y:J→ Ket I)(m:ℕ)(L: List J)(h:L.length ≤ m)(p:∀ i ∈ L,‖X i‖ ≤ K)(q:∀ i∈L,‖Y i‖≤ K)(v:∀ i∈L, ‖X i - Y i‖≤ d) : ‖rollC (pieceV a X) L-rollC (pieceV a Y) L‖≤ m*K^m*d:=by
 have k0:0 ≤ K:= zero_le_one.trans g
 have he: ‖rollC (pieceV a X) L-rollC (pieceV a Y) L‖≤ L.length*K^L.length*d:=by
    induction L with
    | nil => simp [rollC]
    | cons i L ih =>
       let A:=pieceV a X i; let B:=pieceV a Y i; let H:=rollC (pieceV a X) L; let Z:=rollC (pieceV a Y) L; let u(j:J)(t:j∈L):j∈ i:: L:=List.mem_cons_of_mem i t
       have ht: ‖A‖≤ K:= (Flare.cost_pe ..).trans (p _ List.mem_cons_self); have hL : L.length≤ m:=Nat.le_of_lt h; have hf: ‖Z‖ ≤ K^L.length:= lick a _ k0 fun i t=> q i (u i t); have hg:‖A-B‖≤ d:= (creed_delta (a i) ..).trans (v i List.mem_cons_self)
       have hx: ‖H-Z‖≤ L.length*K^L.length*d:= ih hL (fun j v=> p j (u j v)) (fun j v=>q j (u j v)) (fun j h=> v j (u j h))
       change ‖A*H-B*Z‖≤_; rw [show A*H-B*Z= A*(H-Z)+(A-B)*Z from (by rw [mul_sub,sub_mul]; abel)]
       apply (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul ht hx (norm_nonneg _) k0)) ((norm_mul_le ..).trans (mul_le_mul hg hf (norm_nonneg _) ds))).trans ?_)
       rw [List.length_cons,pow_succ,Nat.cast_add,Nat.cast_one]; linarith only [mul_le_mul_of_nonneg_right g (show 0≤K^L.length*d by positivity)]
 apply he.trans; gcongr
section budget
variable {N:Lattice.Side}
open Lat Cube Tulip
local notation "So"=> Single N
local notation "F0"=>FC So
local notation "IC"=> Creduct So
variable {P E A B:Op (Single N)}{u:UNI (Single N)}{v Ω:Wave (Single N)}
abbrev forgeF (P A B:Op So)(U:UNI So)(b:ℝ)(i:IC): Ket So:= acts (if i.1 then star (onePeak P B U b) else oneWarp P A U b) (basisKet i.2)
abbrev graveF (P A B:Op So)(U:UNI So)(b ε:ℝ)(i:IC):= acts (1-lowCut N ε) (forgeF P A B U b i)
lemma low_taste (a:PurchB C D b (oneWarp P A u b))(c:PurchB C D b (star (onePeak P B u b))) (i:IC) {ε:ℝ}(e:0<ε): let x:=forgeF P A B u b i; let y:=graveF P A B u b ε i
    ‖x‖≤D∧ ‖y‖≤D ∧ ‖x-y‖≤ C*ε:=by
 intro x y; let p:= if i.1 then star (onePeak P B u b) else oneWarp P A u b; have h:PurchB C D b p:=by unfold p; split_ifs; exact c; exact a
 have hv:= from_local h i.2
 have hx:‖x-y‖ ≤ C*ε:=by
    unfold y graveF; rw [act_sub,act_one,show x=forgeF P A B u b i from rfl, sub_sub_cancel]; unfold forgeF; rw [← act_mul];
    exact (h.1 i.2.1.1 (basisKet i.2) (by simp [basisKet]) (fun k v=> by
       rw [basis_apply,if_neg ?_]; intro z; apply v; rw [z]; exact mem_filter.mpr ⟨mem_univ _,rfl⟩)).2 _ e.le
 exact ⟨hv,((Flare.opy ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((low_project N ε).one_sub.norm_le _)).trans hv)),hx⟩

def debitW (P A B:Op So)(U:UNI So)(b ε:ℝ)(v:Wave So)(i:IC)(t:Bool) := ‖acts (dustAnn t P (graveF P A B U b ε i)) v‖
def influence (P A B:Op So)(U:UNI So)(b ε:ℝ)(S:Finset So)(v:Wave So):= ∑ i∈S, ∑ c:Bool,∑ t:Bool,(debitW P A B U b ε v (c,i) t)^2
lemma influence_pos (S:Finset So)(v:Wave So) {ε:ℝ} : 0≤ influence P A B u b ε S v:= sum_nonneg fun i _=>sum_nonneg fun c _=>sum_nonneg fun t _=> sq_nonneg _
lemma credit_paid (S:Finset So)(i:IC)(p:i.2∈ S)(s:Bool){ε:ℝ} : debitW P A B u b ε v i s ≤ Real.sqrt (influence P A B u b ε S v):=by
 unfold debitW; apply Real.le_sqrt_of_sq_le; apply le_trans (b:= ∑ t:Bool,(debitW P A B u b ε v i t)^2)
 · exact single_le_sum (f:=fun t=> (debitW P A B u b ε v i t)^2) (fun i _=>sq_nonneg _) (mem_univ s)
 apply le_trans (b:= ∑ c:Bool,∑ t:Bool,(debitW P A B u b ε v (c,i.2) t)^2)
 · exact single_le_sum (f:=fun c=>∑ t:Bool, (debitW P A B u b ε v (c,i.2) t)^2) (fun i _=>sum_nonneg (fun _ _=>sq_nonneg _)) (mem_univ i.1)
 unfold influence; exact single_le_sum (f:=fun i=> ∑ c:Bool,∑ t:Bool,(debitW P A B u b ε v (c,i) t)^2) (fun _ _=>sum_nonneg fun i _=>sum_nonneg fun j _=>sq_nonneg _) p
lemma impact (h:IsStarProjection P)(a:PurchB C D b (oneWarp P A u b))(c:PurchB C D b (star (onePeak P B u b))) (S:Finset So)(v:Wave So) {ε:ℝ}(e:0<ε) : influence P A B u b ε S v ≤ 4 *((C/ε)^2*febrile P v):=by
 let X(i):= if (i:Bool) then star (onePeak P B u b) else oneWarp P A u b; let Y(i:Bool):= (1-lowCut N ε)* X i
 have he(j:Bool):PurchB C D b (X j):=by unfold X; split_ifs; exact c; exact a
 have hp(j t:Bool):∑ i∈S,(debitW P A B u b ε v (j,i) t)^2 ≤ (C/ε)^2*febrile P v:=by
    have hg:fitV S (fun i=>graveF P A B u b ε (j,i)) ((C/ε)^2):=by
       have hh:= fit_move S _ (fit_mono univ _ (tollSafe (I:=So)) (subset_univ S) le_rfl) zero_le_one (show ‖Y j‖≤ C/ε from (he j).2 ε e)
       rw [one_mul] at hh; unfold fitV at hh; unfold Y at hh; simp_rw [act_mul] at hh; exact hh
    exact dust_wallet S v _ hg (sq_nonneg _) h t
 unfold influence; rw [sum_comm]; simp_rw [sum_comm (s:=S)];
 apply le_trans (sum_le_sum (fun i _=>sum_le_sum (fun j _=>hp i j))) (le_of_eq ?_); simp; ring
abbrev painW (S: Finset So) (L:List IC):Prop:=∀ i∈L,i.2∈S
lemma thought (f:Valve P E A B)(h:IsStarProjection P)(t:Sea P Ω)(w:‖v‖=1)(hC:0≤C)(hk:1≤K)
 (a:PurchB C D b (oneWarp P A u b))(c:PurchB C D b (star (onePeak P B u b))) (g:D≤ K) (S:Finset So)(L:List IC)(p:painW S L) {ε:ℝ}(e:0<ε) (m:ℕ)(l:L.length≤ m):
 let Y:= translateW P A B u b (rollC RootBay L)
 let y:=Real.sqrt (influence P A B u b ε S v)
 ‖quotation v Y-quotation Ω Y‖ ≤ predrawn K m*y+ 2*((m:ℝ)*K^m*(C*ε)):=by
 intro H x; let Y:= graveF P A B u b ε; let Z:=forgeF P A B u b; let A:=rollC (pieceV Prod.fst Y) L; let R:=(m:ℝ)*K^m*(C*ε)
 have hb(i:IC): translateW P _ B u b (RootBay i)=pieceV Prod.fst Z i:= warp_root f h _
 have hp(i:IC): ‖Y i‖≤ K:= ((low_taste a c i e).2.1).trans g
 have hL:H= rollC (pieceV Prod.fst Z) L:=by unfold H; rw [warp_word f h, funext hb]
 have hv: ‖H-A‖ ≤ R:=by rw [hL]; exact pearl_walk hk (mul_nonneg hC e.le) Prod.fst Z Y m L l (fun i _=>(low_taste a c i e|>.1).trans g) (fun i _=>hp i) (fun i _=> (low_taste a c i e).2.2)
 have he: ‖quotation v A-quotation Ω A‖≤ predrawn K m*x:=wick_Rate Prod.fst Y h t v w hk (Real.sqrt_nonneg _) m L l (fun i _=>hp i) (fun i h s=>credit_paid S i (p i h) s)
 let Q:= quotation v; let Z':=quotation Ω
 have hc:‖Q H-Q A‖ ≤ R:= by unfold Q; rw [←quot_sub v H A]; exact (quot_cost _ w _).trans hv
 have hl:‖Z' H-Z' A‖ ≤ R:= by unfold Z'; rw [←quot_sub Ω H A]; exact (quot_cost _ t.2 _).trans hv
 change ‖Q H-Z' H‖≤_ ; rw [show Q H-Z' H=Q A-Z' A+(Q H-Q A)-(Z' H-Z' A) by abel]; exact (norm_sub_le ..).trans (((add_le_add ((norm_add_le ..).trans (add_le_add he hc)) hl)).trans_eq (by unfold R; ring))
end budget
end YM.CF.Fock.Flux
end
