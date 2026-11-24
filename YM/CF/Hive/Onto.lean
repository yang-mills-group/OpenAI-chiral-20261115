import YM.CF.Hive.Fan
set_option autoImplicit false
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
variable {N B m L:Side}{S: Seal (Skye.Seat N)}{k j:ℕ}{a b d c e H:ℝ}
abbrev Beta:=SpinIdx × Slot
abbrev Play:=Beta×Beta
abbrev Tones (N:Side):= Oboe (Single N)
abbrev feed (w:Single N):Site N:= w.1.1
abbrev note (y:Site N)(i:Beta):Single N:=((y,i.1),i.2)
abbrev callP(s:Sweep N)(v:Tones N):Site N:=(Tofu (castX s) N).symm (feed v.2)
abbrev rangeH(s:Sweep N)(v:Tones N)(i:Beta): Tones N:=(v.1.xor (detX s.s), note (callP s v) i)
lemma home_l(s:Sweep N)(v:Tones N) :boxA s (node (callP s v))= home_n N v.2:=by
 let y:=callP s v; rw [show boxA s (node y)=node (Tofu (castX s) N y) from (Shape.nodex ..).symm]; exact congrArg node ((Tofu ..).apply_symm_apply _)
lemma restDrop {n:Type*}[LinearOrder n][Fintype n]{p q:n}{U:UNI n}(h:U.val p q=0)(b c:Bool): (crib U b c).val p q=0:=by cases b<;> cases c<;> simp [h, Pastry.thread,crib, ccU,filmG]
variable (s:Sweep N)(U:Ids N)
abbrev dustE(i:Tones N)(x:Beta):ℂ:=let V:=siteU (castX s) s.charge (spinU s.charge s.s) N; (crib V (detX s.s) i.1).val (note (callP s i) x) i.2
abbrev rootE(i:Tones N)(x:Beta):Tones N:=(i.1,note (feed i.2) x)
abbrev durE(g: Seat N→ E)(i:Tones N)(x:Beta):ℂ:= (crib (tradew N g) false i.1).val (note (feed i.2) x) i.2
lemma moneyA{i:Site N}{f:Single N→FC (Single N)}(p:∀ w,feed w≠i→f w=0): ∑ v:Single N,f v= ∑ j:Beta,f (note i j):=by
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single i,Fintype.sum_prod_type]; intro a _ h; apply sum_eq_zero; intro j _; exact sum_eq_zero fun k _=> p _ h; simp
lemma dust_t(i:Tones N): teen s (bell i)=∑ v:Beta,dustE s i v • bell (rangeH s i v):=by
 obtain ⟨v,g⟩:=i; unfold teen yodel; rw [mile]; apply moneyA (i:=callP s (v,g)); intro w h; rw [show (crib _ _ _).val w _=0 from ?_,zero_smul]; apply restDrop; change ((mealU (castX s) (spinU ..) (xtra s.charge) N).val _ _)=0; simp only [mealU,portX,jump_apply]; split; next p=>
   apply False.elim (h _); apply (Tofu (castX s) N).injective; exact Eq.trans p ((Tofu ..).apply_symm_apply _).symm
 rfl
lemma dure_t (g: Seat N→ E)(i:Tones N): Gaze g (bell i)=∑ v:Beta,durE g i v • bell (rootE i v):=by
 obtain ⟨v,t⟩:=i; unfold Gaze; rw [mile,sound]; simp_rw [Bool.xor_false]; apply moneyA (i:=feed t); intro w h; rw [show (crib _ _ _).val w _=0 from ?_,zero_smul]; apply restDrop; unfold tradew; dsimp only; rw [jump_apply]; split; next p=> exact (h (congrArg Prod.fst (show w.1=t.1 from p))).elim
 rfl
-- tends.B
abbrev hol(i:Tones N)(x:Play):Tones N:=rangeH s i x.2
abbrev peso(i:Tones N)(x:Play):ℂ:= let h:= rangeH s i x.1; dustE s i x.1 * durE ((frameP U)⁻¹) h x.2
lemma ageA(S:Seal (Skye.Seat N))(i:Tones N): mallC S U (bell i) = ∑ x:Play,peso (chip S U)⁻¹ U i x • bell (hol (chip S U)⁻¹ i x):=by
 rw [mallC,RingHom.comp_apply,dust_t,map_sum]; simp_rw [show ∀ g: Skye.Seat N→ E,∀ (x:ℂ)(p:FC (Single N)), Gaze g (x • p)= x • Gaze g p from fun g x p=> lot_s ..,dure_t, Finset.smul_sum,smul_smul]; rw [Fintype.sum_prod_type (f:=fun p:Play=>peso (chip S U)⁻¹ U i p • bell (hol (chip S U)⁻¹ i p))] -- tune
lemma paycheck(i:Tones N)(x:Play): ‖peso s U i x‖≤1:=by
 have hp(p:UNI (Single N))(i j):‖p.val i j‖≤1:=(norm_entry ..).trans (CStarRing.norm_of_mem_unitary p.property).le
 unfold peso; dsimp only; rw [norm_mul]; apply mul_le_one₀; exact hp (crib (siteU (castX s) s.charge (spinU s.charge s.s) N) (detX s.s) i.1) _ _; exact norm_nonneg _; let K:=rangeH s i x.1; exact hp (crib (tradew N (frameP U)⁻¹) false K.1) _ _
lemma grape_l(g f:Seat N→E) (i:Tones N)(v:g (home_n N i.2)= f (home_n N i.2))(x: Beta): durE g i x= durE f i x:=by
 unfold durE; let Y:= note (feed i.2) x; have he:(tradew N g).val Y i.2=(tradew N f).val Y i.2:=by
    unfold tradew; dsimp only; rw [jump_apply,jump_apply]; split; next h=>
     exact congrArg (fun z:SU.E=> (matter z).val Y.2 i.2.2) v
    rfl
 obtain ⟨b,w⟩:=i; cases b; exact congrArg star he; exact he
lemma peso_p (Y:Ids N)(i:Tones N)(x:Play)(p:node (callP s i)∈S)(g:Set.EqOn U Y S): peso s U i x=peso s Y i x:=by unfold peso; dsimp only; apply congr_arg (_ * ·); apply grape_l; simp only [frameP,Pi.inv_apply, show home_n N (rangeH s i x.1).2=node (callP s i) from rfl]; rw [g p]
end YM.CF.Hive
