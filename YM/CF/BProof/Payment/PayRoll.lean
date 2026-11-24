import YM.CF.BProof.Payment.Meter
import YM.CF.BProof.Release.Gain
/-! Keep complex law, assemble unpaid Spin and Restore through full Angular reissue. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Payment
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular Anthem Girt
open Vault Paige Drapes Moment RG Wilson Charge
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {m B L:Side}{j:ℕ}{p: Odd L.val}{V: Pricing j L p (Vault.Thread j)}{δ:ℝ}(D:GramM (mid m B))(W:Grasp V B δ)(F:Loom (mid m B)) {Y:Yard (More (mid m B))}{I:Type}[Fintype I](Q:Score Y I)
local instance (I : Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
variable {A C C' R μ ν:ℝ}
set_option quotPrecheck false
local notation "N_"=> mid m B

structure Lifted(A C C' μ R ν:ℝ): Prop where
 grant: Q.Budget A C C'
 flow:D.path.Bounds D.funds μ R ν
 beta:0≤D.beta
 proper : Envelope (denZ D W F)
 ward :∀ g x, denZ D W F (gird g x)= effectK (tradew N_ g).val (denZ D W F x)
-- intentionally canceled Mark mask inside F. Contains exp(big) so suit restores. Exponent cancels big upon Big-exp. No cutoff replacement
variable (Y) in
def heavyG (M:ℕ):= big Y D.funds D.p D.path M D.beta
def ask (z:Orbit (mid m B))(b:Y.FaceS)(M:ℕ):ℂ:=  Complex.exp ((heavyG D Y M z.1:ℂ)+Q.exponent univ z.1 b) *inner ℂ (mateK N_) (acts ((Madd (Q.SBook z.1 b)).prod (Score.chamber Y univ)) (ket₀ D W F z))
variable (M:ℕ)
def inside (U:Pane N_)(v:Y.FaceS):=∫ x, ask D W F Q (U,x) v M ∂depot N_
def senate (f:Y.Glyph)(U:Pane N_) := Y.selected Q.y Q.S f (Y.selcost Q.y Q.S (Release.suit (M:=M) (c:=D.funds) Y D.path D.p D.beta (inside D W F Q M))) U
lemma billing (U:Pane N_): (∫ x, read₀ D W F Q.test (U,x)∂depot N_)=∫ x,(∑ p:Y.Glyph, (if Y.accepted Q.y Q.S U p then Y.selcost Q.y Q.S (fun U r=> Release.suit (M:=M) (c:=D.funds) Y D.path D.p D.beta (fun U r=>ask D W F Q (U,x) r M) U r) U (Y.sweepLabel Q.y Q.S U p) else 0))∂depot N_:= by
 refine integral_congr_ae (Eventually.of_forall fun x=>?_) -- tune using conv
 dsimp only; unfold read₀; dsimp only; rw [Q.score_test U]; unfold beamZ; rw [act_sum,inner_sum,Finset.sum_filter]; apply sum_congr rfl; intro i hi; split_ifs; rename_i w; rw [Q.songs]; unfold ask Release.suit Angular.Yard.selcost Score.words; rw [act_smul,inner_smul_right]; simp_rw [Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg]; -- combine exp
 rw [mul_assoc (↑(_) :ℂ), ←mul_assoc (Complex.exp _),←Complex.exp_add,heavyG]; ring_nf -- tune abel_nf
 rfl
variable (h:Lifted D W F Q A C C' μ R ν)
include h
lemma ask_m : Envelope (uncurry (fun U v=> ask D W F Q U v M)):=by
 let k:= Orbit N_ × Y.FaceS; let q (i:k):=(i.1.1,i.2); have hq:Measurable q:=by unfold q; fun_prop
 let L(i:k):= acts ((Madd (Q.SBook i.1.1 i.2)).prod (Score.chamber Y univ)) (ket₀ D W F i.1); have he: Envelope L:=by
   let P(i:k):= (Madd (Q.SBook i.1.1 i.2)).prod (Score.chamber Y univ); apply kitE P (fun i=> ket₀ D W F i.1) (fun (x:FC (Single N_))(y:Phys N_)=> acts x y) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd)  (show Envelope P from ?_); swap
   · change Envelope ((fun p:Pane N_× Y.FaceS=> (Madd (Q.SBook p.1 p.2)).prod (Score.chamber Y univ)) ∘ q) ; exact Law.pull (crop_m Q) hq
   exact snap (X:=(Prod.fst : k→Orbit N_)) (pole_w (denZ D W F) (fun u=>Complex.exp (-D.v) • u) (Continuous.const_smul continuous_id (Complex.exp (-D.v))) h.proper) measurable_fst
 let R0:= fun i:k=> Complex.exp ((heavyG D Y M i.1.1:ℂ)+Q.exponent univ i.1.1 i.2); have hv:Envelope R0:=by
    apply kitE (fun i:k=>heavyG D Y M i.1.1) (fun i:k=> Q.exponent univ i.1.1 i.2) (fun x a=> Complex.exp ((x:ℝ) +a)) (by unfold uncurry; fun_prop); exact snap (X:=fun i:k=>i.1.1) (bigEnv D.path D.beta Y D.p M h.flow h.beta) (measurable_fst.comp measurable_fst); exact snap (X:=q) (holePay Q h.grant univ) hq
 exact kitE R0 L (fun a b=>a*inner ℂ (mateK N_) b) (by unfold uncurry; fun_prop) hv he
lemma insideEnvelope : Envelope (uncurry (inside D W F Q M)):= Law.fund (depot N_) (f:=fun p:(Pane N_×Y.FaceS)× Ids N_=> ask D W F Q (p.1.1,p.2) p.1.2 M) (snap (ask_m D W F Q M h) (X:=fun p:(Pane N_×Y.FaceS)× Ids N_=> ((p.1.1,p.2),p.1.2)) (by fun_prop))
lemma senate_env (f:Y.Glyph): Envelope (senate D W F Q M f):= Y.select_pay Q.y Q.S f _ (Y.selcost_ep Q.y Q.S _ (Release.suited Y D.path h.flow D.p D.beta (inside D W F Q M) (insideEnvelope D W F Q M h) h.beta) h.grant.xi)
lemma prime (U:Pane N_): (∫ x, read₀ D W F Q.test (U,x)∂depot N_)=∑ p:Y.Glyph, senate D W F Q M p U:= by
 rw [billing D W F Q M, integral_finsetSum]; swap
 · intro i _; split_ifs; swap; apply integrable_zero
   unfold Angular.Yard.selcost Release.suit; apply Integrable.smul; apply Integrable.smul; exact Law.pay (snap (ask_m D W F Q M h) (X:=fun x:Ids N_=> ((U,x),Y.sweepLabel Q.y Q.S U i)) (by fun_prop))
 apply sum_congr rfl; intro i _; unfold senate Angular.Yard.selected Angular.Yard.selcost Release.suit inside; split_ifs; rw [integral_smul,integral_smul]; exact integral_zero ..
-- ward spin and tags only after summing faces. whole representation on squashed + dummy p
lemma ground (U:Pane N_)(t:Geometry N_)(u:Y.Frozen t): (∫ x, read₀ D W F Q.test (U,x)∂depot N_)=∫ x, read₀ D W F Q.test (gauge t U,x)∂depot N_:=by
 let A(x:Ids N_): ℂ:= read₀ D W F Q.test (gauge t U,x)
 have he(x:Ids N_): read₀ D W F Q.test (U,x)=A (threadG t x):=by
   let z:Orbit N_:=(U,x); let Q':= tradew N_ t; let v:=quantU Q'; let k:= Complex.exp (-D.v)
   have hu: acts v.val (ket₀ D W F z)= ket₀ D W F (gird t z):= by rw [ket₀,ket₀,map_smul,h.ward]; rfl
   let Y:=mateK N_; change inner ℂ Y (acts (Q.test U) (ket₀ D W F z))=inner ℂ Y (acts (Q.test (gauge t U)) (ket₀ D W F (gird t z)))
   rw [← act_unit_inner v Y (acts (Q.test U) (ket₀ D W F z)), swivel, show twist v (Q.test U)=_ from Q.test_spin U h.grant t u,hu,show acts v.val Y=Y from Girt.mastC t] -- tune synth
 simp_rw [he]; exact Law.apply_pres (threads t) ((read₀_envelope D W F h.proper Q.test (Q.test_env h.grant)).meas.comp (measurable_const.prodMk measurable_id))
lemma hindi : numerator D W F Q.test= ∑ p:Y.Glyph,∫ x, senate D W F Q M p (Y.squash x)∂prior SU.group (More N_):=by
 unfold numerator; rw [Y.sweep_out (depot N_) _ (read₀_envelope D W F h.proper Q.test (Q.test_env h.grant)) (fun t u x=> ground D W F Q h _ _ u)]; simp_rw [prime D W F Q M h]; rw [integral_finsetSum]; intro i _; exact Law.pay (Law.pull (senate_env D W F Q M h i) Y.squash_c) -- tune
end YM.CF.BProof.Payment
