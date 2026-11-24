import YM.CF.BProof.Anthem.Roll
import YM.CF.BProof.Anthem.Tariff
-- product over Y.index noncommProd in observed space, canonical expansions and size
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Anthem
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular
open Vault Paige Drapes Moment RG Wilson
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I]{Y:Yard (More N)}
local instance (I : Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
-- across adjacent bands
lemma twinBars(Y:Yard (More N)): Pairwise (Disjoint on Y.band):= fun i j u=> disjoint_left.mpr (fun _ h v=> u ((codeB Y h).2.symm.trans (codeB Y v).2))
lemma harmony (S: Y.Index→Obs N)(h:∀ i,Allowed (Y.band i) (S i)): Pairwise (Commute on S):= fun i j u=>(h i).commute (h j) (twinBars Y u) -- optional transfer
namespace Score
variable (Q:Score Y I)(x:Pane N)(b:Y.FaceS)
lemma lords {i j:Y.Index}(h:i≠j): Disjoint (inn Y i) (inn Y j):= disjoint_left.mpr (fun _ u t=>disjoint_left.mp (twinBars Y h) ((mem_filter.mp u).2) ((mem_filter.mp t).2))
lemma across {i j:Y.Index}(h:i≠ j):Disjoint (modes (Y.band i)) (modes (Y.band j)):= by rw [inn_scope i,inn_scope j]; exact stake_umbrella (lords h)
lemma commence : Pairwise (Commute on fun i=> Q.partOp i x (b i)):= fun i j u=> council (Q.partOp_modes i x _) (Q.partOp_modes j x _) (across u)
lemma rollCall : Pairwise (Commute on fun i=> Q.slot i x):= fun i j u=> council (Q.slot_modes i x) (Q.slot_modes j x) (across u)
def waltz (S:Finset Y.Index) (x:Pane N):= edgeP (fun i=> Q.slot i x) (Q.rollCall x) S
def test : Obs N:= Q.waltz univ
def jointOp(S:Finset Y.Index) := edgeP (fun i=> Q.partOp i x (b i)) (Q.commence x b) S
def scaleBook (p:Site (More N)) : Stamp := Q.H (hr Y p) x (b (hr Y p)) p
def SBook (p:Site (More N)):Stamp:= if Trek.dark Y p then Q.scaleBook x b p else northW N p -- needed: support of Ms H beyond band in gaps DON'T read through nearest N. important for maps! keep inert. variant must not evaluate HN beyond band.
def crop : Plant N:= Madd (Q.SBook x b)
lemma timbre(i:Y.Index)(p:Site (More N))(h:p∈Y.band i): Q.SBook x b p= Q.H i x (b i) p:=by unfold SBook scaleBook; rw [if_pos (codeB Y h).1,(codeB Y h).2]
lemma healthy(p:Site (More N)): SealH (Q.SBook x b p):=by unfold SBook; split; exact Q.H_seal _ _ _ _; exact north_seal _
variable (Y) in
def chamber (S:Finset Y.Index) : Support N:= S.biUnion (inn Y)
lemma darkCh(x: Site N): x∈ chamber Y univ ↔ Trek.dark Y (node x):=by
 unfold chamber; constructor; intro t; obtain ⟨i,p,h⟩:= mem_biUnion.mp t; exact (codeB Y (mem_filter.mp h).2).1
 intro v; exact mem_biUnion.mpr ⟨_,mem_univ _,mem_filter.mpr ⟨mem_univ _,band_pick Y _ v⟩⟩
def exponent (S:Finset Y.Index) (x:Pane N)(b:Y.FaceS): ℂ:= ∑ i∈ S, ((Q.gaugeCharge i x:ℂ)- Q.mask i x (b i))
def words := (Y.owed Q.y Q.S x b:ℂ)*Complex.exp (Q.exponent univ x b)
lemma chorus (S:Finset Y.Index) : Q.jointOp x b S=(∏ i∈S,Q.amt i x (b i)) • (Q.crop x b).prod (chamber Y S):=by
 induction S using Finset.induction_on with
 | empty=> simp [jointOp,chamber]
 | insert i S h ih=>
   have hp:Disjoint (inn Y i) (chamber Y S):= by rw [chamber, disjoint_biUnion_right]; exact fun j tj=> lords (fun u=> h (u.symm ▸ tj)) -- tune
   unfold jointOp; rw [edgeP_cons _ _ S i h]; change _*Q.jointOp x b S=_
   have hx:chamber Y (insert i S)=inn Y i∪chamber Y S:=by rw [chamber,biUnion_insert,chamber]
   have ht:(Madd (Q.H i x (b i))).prod (inn Y i)= (Q.crop x b).prod (inn Y i):= Madd_here (fun j g=> (Q.timbre x b i _ (mem_filter.mp g).2).symm)
   rw [ih,hx,Plant.splice _ hp,prod_insert h,mul_smul,partOp,ht, Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
lemma songs : Q.jointOp x b univ=Q.words x b • (Madd (Q.SBook x b)).prod (chamber Y univ):=by
 rw [Q.chorus x b]; unfold crop words; congr 1 -- tune scalar equality
 unfold exponent amt Angular.Yard.owed; rw [Complex.exp_sum, Complex.ofReal_prod, prod_mul_distrib]; simp_rw [Q.fork] -- tune
lemma cards (f:Y.Glyph): f∈ roll 0 (fun i:Y.Index=> Q.named i x) univ ↔ Y.accepted Q.y Q.S x f:=by rw [roll_s]; simp only [mem_univ,ite_true]; unfold named; apply forall_congr'; intro i; split; exact mem_singleton; exact Iff.rfl
lemma score_test : Q.test x= ∑ f:Y.Glyph with Y.accepted Q.y Q.S x f, Q.jointOp x (Y.sweepLabel Q.y Q.S x f) univ:=by
 let F : Finset Y.Glyph:=roll 0 (fun i=>Q.named i x) univ; let V(i:Y.Index)(j:Angular.Signs (More N)):=Q.partOp i x (Q.basisLabel i x j); rw [show Finset.filter _ (univ:Finset Y.Glyph)=F from ?_]; exact noncomm_sumSet 0 (fun i=>Q.named i x) V (fun f:Y.Glyph=> Q.commence x (Y.sweepLabel Q.y Q.S x f)) (Q.rollCall x) univ -- tune binder duplicate
 ext f; simp only [F,mem_filter,mem_univ,true_and, cards Q x f]
variable {A B C:ℝ}(h:Budget Q A B C)
include h
lemma test_spin (g: Geometry N)(u:Y.Frozen g): twist (quantU (tradew N g)) (Q.test x)= Q.test (gauge g x):=by
 unfold test waltz edgeP; rw [map_noncommProd]; exact noncommProd_congr rfl (fun i (_:i∈univ)=> Q.slot_rot i x h g u) _
lemma test_pairwise : Pairwise (Commute on Q.slot):= harmony Q.slot (fun i=>Q.allowed i h)
lemma test_eq : Q.test=edgeP Q.slot (Q.test_pairwise h) univ:=by
 have hp (S:Finset Y.Index)(x:Pane N): Q.waltz S x=edgeP Q.slot (Q.test_pairwise h) S x := by -- edgeP has Semiring Obs (yes)
    induction S using Finset.induction_on with
    | empty=> simp [waltz]
    | insert i S u ih=> unfold waltz; rw [edgeP_cons _ _ _ _ u,edgeP_cons _ _ _ _ u,Pi.mul_apply]; rw [←ih]; rfl
 exact funext (hp _)
omit h in
theorem overProd {D K I:Type}[MeasurableSpace D][NormedRing K][MeasurableSpace K][MeasurableMul₂ K][DecidableEq I][Fintype I] (U:I→ D→ K)(h:∀ x:D,Pairwise (Commute on fun i=>U i x))(p:∀ i, Envelope (U i))(S:Finset I): Envelope (fun x=>edgeP _ (h x) S):=by
 induction S using Finset.induction_on with| empty=> simp_rw [edgeP_nil]; exact ⟨measurable_const,_,fun _=> le_rfl⟩| insert i S u ih=> simp_rw [edgeP_cons _ _ S i u]; obtain ⟨A,g⟩:=(p i).cost; obtain ⟨B,h⟩:= ih.cost; exact ⟨(p i).meas.mul ih.meas, A*B,fun i'=> (norm_mul_le ..).trans (mul_le_mul (g i') (h i') (norm_nonneg _) ((norm_nonneg _).trans (g i')))⟩
lemma test_env : Envelope Q.test:=overProd _ Q.rollCall (fun i=> (Q.allowed i h).bounded) univ
end Score
end YM.CF.BProof.Anthem
