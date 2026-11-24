import YM.CF.Hive.Onto
set_option autoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye MeasureTheory
variable {N B m L:Side}{S: Seal (Skye.Seat N)}{j k:ℕ}{v a b d c e H:ℝ}
variable (s:Sweep N)(U:Ids N)
def DeckU : List (Tones N)→ Type
| []=>Unit
| _::l=> Play×DeckU l
def bunchF : ∀ i:List (Tones N), Fintype (DeckU i)
| []=> inferInstanceAs (Fintype Unit)
| _::l=> @instFintypeProd _ _ _ (bunchF l) -- tune
attribute [instance] bunchF
lemma hallN(D:List (Tones N)) : Fintype.card (DeckU D)=(Fintype.card Play)^D.length:=by
 induction D with| nil=>exact (Eq.trans (show Fintype.card (DeckU ([]:List (Tones N))) = Fintype.card Unit from rfl) (by simp))| cons i D h=> rw [List.length_cons,pow_succ',show Fintype.card (DeckU (i::D))=Fintype.card (Play × DeckU D) from rfl,Fintype.card_prod,h]
def castJ : (D: List (Tones N)) → DeckU D → List (Tones N)
| [],_=>[]
| i::D,z=> hol s i (Prod.fst z) :: castJ D (Prod.snd z)
def jive : (D:List (Tones N))→DeckU D→ℂ
| [],_=>1
| i::D,z=> peso s U i (Prod.fst z) * jive D (Prod.snd z)
lemma tick_size (D:List (Tones N))(z:DeckU D): (castJ s D z).length=D.length:=by induction D with| nil=>rfl| cons i D h=> change (_::castJ s D _).length= _; simp [h] -- induction z generalized automatically
lemma tick_in(D:List (Tones N))(p:∀ i∈D,home_n _ i.2∈ S)(x:DeckU D)(j:Tones N)(h:j∈castJ s D x):home_n _ j.2∈ actS s S:=by
 induction D with
 | nil=> exact False.elim (List.not_mem_nil h)
 | cons i D k=>
   rw [castJ,List.mem_cons] at h; rcases h with rfl|h
   · apply Finset.mem_map.mpr; refine ⟨_,p _ (List.mem_cons_self),?_⟩; change (boxA s).symm (home_n N i.2)= node (callP s i); rw [←home_l s i,Equiv.symm_apply_apply]
   exact k (fun i h=>p i (List.mem_cons_of_mem _ h)) _ h
lemma jive_le(D:List (Tones N))(x:DeckU D): ‖jive s U D x‖≤1:=by
 induction D with
 | nil=>simp [jive]
 | cons i D h=> rw [jive,norm_mul]; exact mul_le_one₀ (paycheck ..) (norm_nonneg _) (h _)
lemma jive_in(D:List (Tones N))(p:∀ i∈D,home_n N i.2∈S)(x:DeckU D){Y: Ids N}(g:Set.EqOn U Y (actS s S)): jive s U D x=jive s Y D x:=by
 induction D with
 | nil=>rfl
 | cons i D h=> rw [jive,jive,h (fun j p'=>p j (List.mem_cons_of_mem _ p')),peso_p s U Y i _ _ g]; simp [actS,home_l,p _ List.mem_cons_self]
lemma swing(S:Seal (Skye.Seat N))(D:List (Tones N)): mallC S U (drum D)= ∑ i:DeckU D,jive (chip S U)⁻¹ U D i • drum (castJ (chip S U)⁻¹ D i):=by
 let s:=(chip S U)⁻¹
 induction D with
 | nil=> rw [show drum (n:=Single N) []=1 from rfl,map_one]; change _=∑ _ :Unit,(1:ℂ)•(1:FC (Single N)); simp
 | cons i D h=>
   let F(x:Play×DeckU D):FC (Single N):= jive s U (i::D) x • drum (castJ s (i::D) x); change _=∑ x:Play×DeckU D,F x; rw [show drum _=bell i * drum D from rfl,map_mul,h,ageA, Fintype.sum_prod_type F,sum_mul]; refine sum_congr rfl fun j _=> ?_ ; rw [mul_sum]; refine sum_congr rfl fun i' _=> ?_; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rfl
-- coat identity
lemma dura_meas (i:Tones N)(x:Beta): Measurable (fun F:Ids N=> durE (frameP F)⁻¹ i x):=by
 let p(F:Ids N)(i: Seat N):= ((F i).2.2)⁻¹; have hp(i):Measurable fun F=> p F i:= (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))).inv
 rcases i with ⟨r,i⟩; let P(F:Ids N):= tradew N (p F); have he(x y):Measurable fun F:Ids N=>(P F).val x y:=by
    unfold P tradew; simp only [jump_apply]; split; swap; exact measurable_const
    have ht: Continuous fun t:E=> (matter t).val x.2 y.2:= ((Continuous.comp (g:=fun z:Op Slot=> z x.2 y.2) (by fun_prop) matter_cont))
    exact ht.measurable.comp (hp _)

 cases r; · exact (continuous_star.measurable.comp (he _ _))
 exact he _ _
lemma pesM(i:Tones N)(x:Play): Measurable (fun F:Ids N=> peso s F i x):=by unfold peso; dsimp only; exact measurable_const.mul (dura_meas ..)
lemma jiveM (D:List (Tones N))(i: DeckU D):Measurable (fun F: Ids N=> jive s F D i):=by induction D with| nil=>exact measurable_const| cons j D h=> simp_rw [jive]; exact (pesM ..).mul (h _)
end YM.CF.Hive
