import GaugeFieldConstruction.Walking
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 35000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Finset Lattice Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B: Op I}{w:Wave I}
variable {K D b:ℝ}{U : UNI I}
lemma knob_com (i:Creduct I)(L:List (Creduct I))(h:∀ j∈L,i.2≠j.2) : RootBay i*rollC RootBay L= ((-1:ℂ)^L.length) • (rollC RootBay L*RootBay i):=by
 induction L with
 | nil=>simp [rollC]
 | cons j l ih=>
    let A:= RootBay i; let B:= RootBay j; let C:= rollC RootBay l
    have he:i.2≠j.2:= h j List.mem_cons_self; have hv:antiB A B=0:=by
       rw [show antiB A B=_ from centSC i.1 j.1 (basisKet i.2) (basisKet j.2)]; simp [laceSC,he,he.symm]
    have hg:A*B= -(B*A):=eq_neg_of_add_eq_zero_left hv
    change A*(B*C)=(( -1:ℂ)^_ ) • ((B*C)*A); rw [←mul_assoc,hg,neg_mul,mul_assoc, show A*C=(( -1:ℂ)^l.length) • (C*A) from ih (fun j v=>h j (List.mem_cons_of_mem _ v)),List.length_cons,pow_succ', Matrix.mul_smul,mul_assoc B,neg_one_mul,neg_smul]
lemma knob_party (L H:List (Creduct I))(e:Even H.length)(h:∀ i∈L,∀ j∈H,i.2≠j.2): Commute (rollC RootBay L) (rollC RootBay H):=by
 induction L with
 | nil=>exact Commute.one_left _
 | cons i l ih=>
    let X:= rollC RootBay H; change Commute (RootBay i*_) X
    apply Commute.mul_left _ (ih fun i v=>h i (List.mem_cons_of_mem _ v)); unfold Commute SemiconjBy; rw [knob_com _ _ (h i List.mem_cons_self), Even.neg_one_pow e,one_smul]
-- order to represent polys. Extensional library, can pay any representation. repetitions, overlaps inside ok.
abbrev SignWave (I:Type*) := ℂ × List (Creduct I)
abbrev motionF (x: SignWave I): FC I:= x.1 • rollC RootBay x.2
def orchestrate (l : List (SignWave I)): FC I:= (l.map motionF).sum
abbrev meterK (l: List (SignWave I)) :ℝ:= (l.map fun x=>‖x.1‖).sum
abbrev nestM (S: Finset I)(m:ℕ)(L:List (SignWave I)):Prop:= ∀ i∈L,Even i.2.length∧ i.2.length≤ m∧ ∀ j∈i.2,j.2∈ S
def pressedF (S:Finset I)(m:ℕ)(K:ℝ)(M:FC I): Prop:=∃ L:List (SignWave I),nestM S m L∧ meterK L ≤ K∧ orchestrate L=M
lemma nest_agrees {S S':Finset I}{m k:ℕ}{L L'}(h: nestM S m L)(j:nestM S' k L')(e:Disjoint S S'): Commute (orchestrate L) (orchestrate L'):=by
 have ht(i :SignWave I)(p:i∈L)(j':SignWave I)(q:j'∈L'):Commute (motionF i) (motionF j'):=by
    refine ((knob_party i.2 j'.2 (j j' q).1 (fun x u y v=> ?_)).smul_left _).smul_right _
    exact fun f=> disjoint_left.mp e (h _ p|>.2.2 x u) (f ▸ (j _ q|>.2.2 y v))
 have hu(J:Type _) (L: List J)(x:J→FC I)(M:FC I)(p:∀ i∈L,Commute M (x i)) : Commute M (L.map x).sum:=by induction L with|nil=>exact Commute.zero_right _|cons i l ih=>exact (p i List.mem_cons_self).add_right (ih fun i v=>p i (List.mem_cons_of_mem _ v))
 exact (hu _ L motionF (orchestrate L') (fun i v=>(hu _ L' motionF _ (ht i v)).symm)).symm -- universe
lemma rampW (P A B:Op I)(C:FC I)(u:UNI I)(b:ℝ): translateW P A B u b C= knight P b*translateW P A B u 0 C*knight P (-b):=by unfold translateW wall seek; rw [knight_start,one_mul,neg_zero,knight_start,mul_one]; simp only [_root_.mul_assoc]
lemma tilt_chars (h:Valve P E A B)(p:IsStarProjection P)(C: FC I)(v:Wave I)(k:Sea P v) : quotation v (translateW P A B U b C)=quotation v (translateW P A B U 0 C):=by
 have hx:=knight_hold p b v k; have he: acts (knight P (-b)) v=v:=knight_hold p _ _ k; rw [rampW]; -- may rewrites right 0? rw rewrites first okay
 unfold quotation; let T:=translateW P A B U 0 C; let L:=knight P b; let K:=knight P (-b); rw [act_mul (L*T),act_mul L,he, ←act_inner L,show star L=L from knight_star p b, hx]

lemma translateW_sum (P A B : Op I)(U: UNI I)(b:ℝ)(S T:FC I): translateW P A B U b (S+T)=translateW P A B U b S+translateW P A B U b T:=by unfold translateW; rw [mul_add,add_mul]

variable {N: Lattice.Side}
variable {P E A B : Op (Single N)}{U:UNI (Single N)}{v Ω:Wave (Single N)}{c e D H x:ℝ}{m:ℕ}{S:Finset (Single N)}
lemma pulse (f:Valve P E A B)(h:IsStarProjection P)
  (a:PurchB c D b (oneWarp P A U b))(b':PurchB c D b (star (onePeak P B U b)))(s:1≤ K)(o:D≤ K){V:FC (Single N)}(u:pressedF S m H V) : ‖translateW P A B U b V‖ ≤ H*K^m:=by
 obtain ⟨L,hL,e,rfl⟩:=u; let Y:=forgeF P A B U b; let T:=translateW P A B U b; let Q(i:Creduct (Single N)):=pieceV Prod.fst Y i
 have hq:0≤ K:= zero_le_one.trans s
 have hv(i:Creduct (Single N)): ‖Y i‖ ≤ K:= by
    cases j:i.1; · unfold Y forgeF; simp only [j,Bool.false_eq_true,ite_false]; exact (from_local a i.2).trans o
    unfold Y forgeF; simp only [j,ite_true]; exact (from_local b' i.2).trans o -- tune syntax
 have hp(J:List (SignWave (Single N)))(hJ:J⊆ L) : ‖T (orchestrate J)‖ ≤ meterK J*K^m:=by
    induction J with
    | nil=> simp [T,orchestrate,meterK,translateW]
    | cons i l ih=>
       have hw:=hL i (hJ List.mem_cons_self); have he: ‖T (motionF i)‖ ≤ ‖i.1‖*K^m:=by unfold T motionF; rw [scale_crest,norm_smul, warp_word f h, show (fun j:Creduct (Single N)=>T (RootBay j))=Q from funext fun i=> warp_root f h i]; exact mul_le_mul_of_nonneg_left ((lick _ Y hq fun i _=> hv i).trans (pow_le_pow_right₀ s hw.2.1)) (norm_nonneg _)
       rw [show T (orchestrate (i::l))=T (motionF i)+T (orchestrate l) from translateW_sum ..]; apply (norm_add_le ..).trans; apply (add_le_add he (ih (fun j p=>hJ (List.mem_cons_of_mem _ p)))).trans_eq; unfold meterK; simp [add_mul]
 exact (hp L (fun j t=>t)).trans (mul_le_mul_of_nonneg_right e (pow_nonneg hq m))
lemma willow (f:Valve P E A B)(h:IsStarProjection P)(t:Sea P Ω)(w:‖v‖=1)
 (hC:0 ≤ c) (a:PurchB c D b (oneWarp P A U b))(b':PurchB c D b (star (onePeak P B U b))) (s:1≤ K)(o:D ≤ K) {V:FC (Single N)}(u:pressedF S m H V)(he:0<x): let T:=translateW P A B U b; let y:=Real.sqrt (influence P A B U b x S v)
 ‖quotation v (T V)-quotation Ω (translateW P A B U 0 V)‖ ≤ H*(predrawn K m*y+ 2*((m:ℝ)*K^m*(c*x))):=by
 intro T y; rw [← tilt_chars (b:=b) f h V Ω t]; obtain ⟨L,hL,e,rfl⟩:=u; let Z:=predrawn K m*y+ 2*((m:ℝ)*K^m*(c*x))
 have hv:0≤Z:=by unfold Z y; have h:=pred_nonneg K (zero_le_one.trans s) m; positivity
 let Q(F:FC (Single N)):= quotation v (T F); let W(F:FC (Single N)):=quotation Ω (T F);
 have hp(J:List (SignWave (Single N)))(hJ:J⊆ L):‖Q (orchestrate J)-W (orchestrate J)‖ ≤ meterK J * Z:=by
    induction J with
    | nil=> unfold Q W T; simp [translateW,orchestrate,quotation,meterK]
    | cons i l ih=>
       have H:=hL i (hJ List.mem_cons_self); have hx: ‖Q (motionF i)-W (motionF i)‖≤ ‖i.1‖*Z:=by unfold Q W motionF T; rw [scale_crest,quot_scale,quot_scale, ←mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (thought f h t w hC s a b' o S i.2 H.2.2 he m H.2.1) (norm_nonneg _)
       let F:=motionF i; let R:=orchestrate l; unfold Q W at ⊢; rw [show T (orchestrate (i::l))=T F+ T R from translateW_sum ..,quot_sum,quot_sum]; change ‖Q F+ Q R-(W F+ W R)‖≤_; rw [show Q F+ Q R-(W F+ W R)=(Q F-W F)+(Q R-W R) by abel]; apply (norm_add_le ..).trans; apply (add_le_add hx (ih (fun j p=>hJ (List.mem_cons_of_mem _ p)))).trans_eq; unfold meterK; simp [add_mul]
 exact (hp L (fun j t=>t)).trans (mul_le_mul_of_nonneg_right e hv)

-- influence sum routed over disjoint test supports. No volume × every-vector bill.
variable {J:Type*}(F:Finset J)
lemma esteem (d:J→ Finset (Single N))(p:Set.PairwiseDisjoint ↑F d)
 (h:IsStarProjection P)(a:PurchB c D b (oneWarp P A U b))(b':PurchB c D b (star (onePeak P B U b)))(v:Wave (Single N))(e:0<x) : (∑ i∈F, influence P A B U b x (d i) v) ≤ 4*((c/x)^2*febrile P v):=by
 apply le_trans _ (impact h a b' (F.biUnion d) v e); unfold influence; rw [sum_biUnion p]
lemma lair (f:J→ℝ)(S:Finset J): (∑ i∈S,f i)^2≤ (S.card:ℝ)*(∑ i∈S,f i^2):=by
 have he:= sum_mul_sq_le_sq_mul_sq S (fun _=> (1:ℝ)) f; simpa using he
lemma hue (d:J→ Finset (Single N))(p:Set.PairwiseDisjoint ↑F d)
 (hq:0 ≤ c)(h:IsStarProjection P)(a:PurchB c D b (oneWarp P A U b))(b':PurchB c D b (star (onePeak P B U b)))(v:Wave (Single N))(e:0<x) : ∑ i∈F, Real.sqrt (influence P A B U b x (d i) v) ≤ Real.sqrt F.card * (2*(c/x)) * Real.sqrt (febrile P v):=by
 let Q(i):= influence P A B U b x (d i) v; have hp:0≤ febrile P v:=febrile_pos h v; have hv:= lair (fun i=>Real.sqrt (Q i)) F; simp_rw [show ∀ i,(Real.sqrt (Q i))^2 = Q i from fun i=>Real.sq_sqrt (influence_pos ..)] at hv
 apply (sq_le_sq₀ (sum_nonneg (fun i _=>by positivity)) (by positivity)).mp; apply hv.trans; apply (mul_le_mul_of_nonneg_left (esteem F d p h a b' v e) (Nat.cast_nonneg _)).trans_eq; rw [mul_pow,mul_pow,Real.sq_sqrt hp,Real.sq_sqrt (Nat.cast_nonneg _)]; ring
end YM.CF.Fock.Flux
end
