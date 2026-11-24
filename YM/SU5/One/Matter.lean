import YM.SU5.One.Tailored

/-!
# Meaning of the local chiral tests in this theorem

**Chirality at input**. These facts are about what is being reconstructed.
Here *not* claiming chirality/completeness of some derived covariant fields
in a spacetime reconstruction. Show the coupling to genuine chiral overlap
polynomials with their signs/lifts and parallel transport. Includes exact
representation at finite volume/cutoff, on the same histories; no independent
spinor PVs or continuum analogue compared in place of them.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch Tenant
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude
open Dial
open Reed (think syms Plain chemical spell Absorb Fine)

section convention
variable {O:Side}

-- UNSMEARED charged marks. Stated on field assignment before taking covariant
-- words. On the cover `creation/removal` plug them with winding. Plus spin
-- is precisely bar variables, minus spin precisely col variables. Use R-term
-- at the sea and the SYMS convention on its chiral polynomial input.
theorem species (x : Site O × SpinIdx) (k : SU.Slot) :
    let i : Tulip.Single O:= (x,k)
    (x.2.val<2 → i∈ Tset O ∧ (syms (Tset O)).term i=Reed.bar i ∧ (think (Tset O)).term i=put i) ∧
      (2≤ x.2.val → i∉ Tset O ∧ (syms (Tset O)).term i=Reed.col i ∧ (think (Tset O)).term i= -takeF i) := by
  intro i; have he: i∈ Tset O ↔ x.2.val<2:= by obtain ⟨x,y⟩:=x; unfold i; rw [Window.mem_Tset]; simp [plusHalf]
  constructor
  · intro g; exact ⟨he.mpr g,if_pos (he.mpr g),if_pos (he.mpr g)⟩
  intro g; let v:=mt he.mp (not_lt.mpr g); exact ⟨v,if_neg v,if_neg v⟩

-- lift info/pitch
lemma matter_time (Λ:Preparation) (s : ℕ) (x : Cover)(i:Axis): location Λ s (nodeC x) i=(2*x i+1:ℝ)/(2*precisionAt Λ s):=by
  unfold location; rw [Tapestry.nodePrint]; ring

-- The gauge group acts on the matter letters in the *same* representation,
-- one conjugated for removal. Compare `tradition`. These equalities are before taking
-- any gauge invariants.
theorem local_charge (J:Calibration) (x:Cover)(b:SpinIdx)(v:SU.Slot) (g:Seat (J.c O) → SU.E)(w:Fields (J.c O)):
    let U:=g (wrap _ (nodeC x)); let N := J.c O; let P := twist (quantU (tradew N g))
    (SU.matter U).val=(1: Op (Fin 3)) ⊗ₖ SU.each (SU.fund U) ∧
    P (creation J x b v O w) = ∑ d:SU.Slot,(SU.matter U).val d v • creation J x b d O (simultaneous g w) ∧
    P (-(removal J x b v O w)) = ∑ d:SU.Slot,star ((SU.matter U).val d v) • (-(removal J x b d O (simultaneous g w))) := by
  intro U N P
  have hx: g (node (wrap N x))=U:=by unfold U; rw [node_of] -- N defeq
  have hz:= tradition (N:=N) x b g v; rw [hx] at hz
  refine ⟨rfl,?_,?_⟩
  · change twist _ (create _) = _; rw [twist_create,hz,map_sum]; apply sum_congr rfl; exact fun t _=> map_smul ..
  rw [map_neg]; change -(twist _ (Fock.remove _)) = _; rw [twist_remove,hz]
  unfold removal Fock.remove; simp_rw [map_sum,star_sum, map_smul,star_smul,smul_neg,Finset.sum_neg_distrib]; rfl

-- At every fixed resolution where the box fits, the native system of first-
-- link local gauge invariant probes is represented in these polynomials.
theorem sightlines (Λ:Preparation)(l : ℕ)(J : Calibration) (s : ℕ) (i : Side) (S : Finset Cover)
    (u: Roomy S (J.c i)) (x: Evaluation (J.c i))
    (p: x∈ Window.localObs (J.c i) (diamonds (Satin.region S (J.c i))) (sitesIn (J.c i) (Satin.region S (J.c i)))) :
    ∃ F:Dome J, pinhole (Dome J) s F∈circum Λ l J false (cells Λ l s S) (Set.univ∩ Set.Iic s) ∧ toMark x= F.val i := by
  obtain ⟨C,h,hx,a⟩:= (Window.mem_localObs x).1 p
  let T:= Satin.region S (J.c i)
  have hp: AtSupport false T (toMark x):= by
     refine AtSupport.fromEval x (Env.compact C) ?_ hx
     intro y z p
     apply h; intro e hy; exact p e (mem_filter.mp hy).2.1 (mem_filter.mp hy).2.2
  obtain ⟨f,w,e,v,_⟩:= completeBay J i S (toMark x) hp u false (fun _=>⟨x,rfl,C⟩) -- order
  exact ⟨_,oneSlotWell Λ J l false (handstamp (cells Λ l s S)) (Set.univ∩ Set.Iic s) _ (show s∈Set.univ∩ Set.Iic s from ⟨Set.mem_univ _, Set.mem_Iic.mpr (Nat.le_refl s)⟩) ((keeps ..).2 ⟨S,w,supported_cells Λ l s S⟩) (v (fun g x=> a g x.1)),e.symm⟩

end convention

section direct
variable {O : Side}
local notation "N"=> Tset O
-- rectangular Grassmann spell identity for any exposed occupancy basis
-- (See artQ. Adapt proof: here at any supplied actual size.)
lemma parchment {P : Op (Single O)}{A : UNI (Single O)}{V' : Op (Single O)}{x : Finset (Single O)}{K' : Wave (Single O)}
    (h:P=twist A (cutM x))(p:Sea P K') (v:V'*P=cutM (Tset O)*P):
    chemical (V' * A.val) (Tset O) x=chemical A.val (Tset O) x∧ ∃ γ:ℂ,‖γ‖=1∧∀ W: FC (Single O),Plain W → γ * spell (syms (Tset O)) A.val (Tset O) x W=inner ℂ (Dial.mateK O) (acts ((think (Tset O)).eval W) K') := by
  have ht : P*A.val= A.val * cutM x:=by rw [h]; exact twist_product ..
  have hv : V'*A.val*cutM x=cutM N*A.val*cutM x:=by rw [mul_assoc,mul_assoc,← ht,← mul_assoc,v,mul_assoc]
  have he(i j)(p:i∈N)(q:j∈x): (V'*A.val) i j= A.val i j:=by
    have hb:= Matrix.ext_iff.mpr hv i j; rw [cutM,Matrix.mul_diagonal,Matrix.mul_diagonal,if_pos q, mul_one,mul_one,cutM,Matrix.diagonal_mul,if_pos p,one_mul] at hb; exact hb
  constructor
  · unfold chemical; congr 1; refine sum_congr rfl fun i p=>?_ ; congr 1; unfold Reed.tote; exact sum_congr rfl fun j q=>by rw [he i j p q]
  let T:=Fock.wedge A.val x; let c:=inner ℂ T K'
  have hp: K'=c • T:=by nth_rw 1 [← p.1]; rw [h]; exact act_twistLine ..
  let B:=basisKet (Tset O); let u:= Dial.mateK O; let d:= inner ℂ B u
  have hs:Sea (cutM N) u:= (Spire.touchP O) ▸ Dial.tickB O
  have hx:u=d • B:=by nth_rw 1 [←hs.1]; rw [cutLine,cut_oneAct]; unfold B d; rw [basis_inner]
  have hk:‖c‖=1:=by have he:=p.2; nth_rw 1 [hp] at he; rw [norm_smul,show ‖T‖=1 from wedge_norm ..,mul_one] at he; exact he
  have hq:‖d‖=1:=by have ht:=hs.2; nth_rw 1 [hx] at ht; rw [norm_smul,show ‖B‖=1 by simp [B,basisKet],mul_one] at ht; exact ht
  refine ⟨star d*c,(by rw [norm_mul,norm_star,hk,hq,one_mul]),fun X h=>?_⟩; rw [Reed.moment _ _ _ _ h]; change star d*c*_ =inner ℂ u (acts _ K'); nth_rw 1 [hx]; -- nth may rewrite d contain u? pretty let
  rw [hp,map_smul,inner_smul_left,inner_smul_right,mul_assoc]; rfl
end direct

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)

section invoice
variable (i k : ℕ)
local notation "N"=> Y.uv k
local notation "r"=> mesh (Y.ir i) Λ.R.L N
local notation "S"=> Journey.side Y i N
variable (v : Pane (Journey.side Y i (Y.uv k)))
local notation "s₀"=> changeM (m:=r) Λ.U v babyM
local notation "A"=> Tset S
local notation "P"=> spar Λ.K.j babyM v
local notation "ℋ"=> frame SU.matter (Cube.links v) (anticut _)
local notation "D"=> Emu.plantH v
local notation "Z"=> bareCore Y i k v
local notation "β"=> (((Y.voyage i).X N).gram N).beta
local notation "e"=> Complex.exp (-((β * basicP Λ.K.top.clip v:ℝ):ℂ))

structure WeylStencil : Prop where
 active : v∈ clearStage Y N
 wears : Z = e • s₀
 hamiltonian : Safe (ℋ).H ∧ P=portW (helix _).symm (projector (ℋ).H) ∧ IsStarProjection P
 sign : Sea P s₀
 columns : (ℋ).overlap * projector (ℋ).H=cutM (upperP (Journey.side Y i N))*projector (ℋ).H
 on_expansion : D * P=cutM A *P
 spellHere (V:UNI (Single (Journey.side Y i N))) (s:Finset (Single (Journey.side Y i N)))(h:P=twist V (cutM s)) :
    chemical (D*V.val) A s=chemical V.val A s ∧
     ∃ c:ℂ, ‖c‖=1 ∧ ∀ (W: FC (Single (Journey.side Y i N))), Plain W →
       bareField (S) (acts ((think A).eval W) Z) = e * (c * Reed.spell (syms A) V.val A s W)

theorem paidWeyl (t:v∈ clearStage Y N): WeylStencil Y i k v := by
  have hc:=Y.equity i k v t
  have Hs := guardedTop Y i k v t
  have hz : Safe (ℋ).H:= Phase.wiel_ok _ Λ.U.baseY Hs
  have hp : (ℋ).overlap * projector (ℋ).H=cutM (upperP (Journey.side Y i N))*projector (ℋ).H:=Reed.kinetic (m:=r) Hs Λ.U.baseY _
  have hZ:= allowedField Y i k t
  have hV:D * P=cutM A *P:=by
    rw [hc.1,←touchP]; unfold tickA Emu.plantH; let M:= love (Journey.side Y i N)
    change M _*M _= M _*M _; rw [←map_mul,←map_mul]; exact congrArg M hp
  refine ⟨t,hZ,⟨hz,hc.1,?_⟩,hc.2,hp,hV,fun V s h=>?_⟩
  · exact Brace.frame_first Λ.U.topB Λ.U.baseY (Λ.U.couture (Λ.J.gran.trans ((Y.voyage i).ownership N).size) Brace.firstM) Hs
  obtain ⟨hx,u,t₁,w⟩:=parchment h hc.2 hV
  exact ⟨hx,u,t₁,fun F p=>by rw [w F p,hZ,bareField,map_smul,inner_smul_right]⟩

theorem readable {U : Evaluation S}{L : Support (More S)} (h:U∈ Window.localObs S (diamonds L) (sitesIn S L)):
    ∃ F: FC (Single S), Plain F ∧ Absorb (modesIn S L) F ∧ (think A).eval F = U v := by
  obtain ⟨F,p,t⟩:= ((Window.mem_localObs _).1 h).2.2.1 v |>.writer
  exact ⟨F,p.packs (subset_univ _),p,t.symm⟩

-- flat at this same top in the grammar (weight is genuine SU link action,
-- no new block or parameter limit). A convention check linking the handed
-- symbol choice, NOT a weak-coupling or regulator-limit comparison.
theorem flat_const :
    (1:Pane (Journey.side Y i (Y.uv k)))∈ clearStage Y N ∧
    spar Λ.K.j babyM (1:Pane (Journey.side Y i (Y.uv k))) = portW (helix _).symm (Lat.fourImage SU.Slot S
      (fun v=> projector (latticeAtoms S v).H)) ∧ (projector (BZ.atom 0).H)= 1-(BZ.atom 0).plus ∧
      (1/2:ℂ) • (1+grading)=cutM plusHalf := by
  have he : (1:Pane (Journey.side Y i (Y.uv k)))∈ clearStage Y N := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u a; obtain ⟨p,_,w⟩:= (flags_spec ..).1 a
    have ht : faceValue (1:Pane (Journey.side Y i (Y.uv k))) p=1:= by simp [faceValue, Lattice.square,Lattice.travel]
    rw [ht,SU.group.chord_one] at w; exact not_lt.mpr ((Y.meter.a N).threshold_pos.le) w
  refine ⟨he,?_,BZ.origin.1,raising.symm⟩
  rw [← project_four SU.matter (Journey.side Y i (Y.uv k))]; unfold Lat.emptyFrame; let F:=(Y.equity i k 1 he).1
  have hu: Cube.links (1:Pane (Journey.side Y i (Y.uv k)))=1:=by funext x; obtain ⟨v,i⟩:=x; simp [Cube.links]
  rwa [hu] at F
end invoice
end YM.CF.Buffered.Afterglow.Tower.One
