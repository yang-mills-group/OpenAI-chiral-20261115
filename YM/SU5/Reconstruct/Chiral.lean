import YM.SU5.Reconstruct.Windows
import YM.CF.Reed.Play
/-!
# Identify all bare chiral insertions for this determining reading

Includes the (with the actual signs) matrix correspondence to Grassmann
integrals POINTWISE in each occupied band frame; there is ONE phase (doesn't
depend on polynomial). Do not integrate this as a positive determinant or
assume these frames vary measurably. Integrability and square readings are
always those of the ACTUAL history. The only microscopic polynomials
identified with continuum representatives so far are the ones measured by
the prescription from a fixed observation, as in Bare.lean. This does not
claim a limit of a new sequence of insertions of bare momentum modes, an
absence of additional continuum degrees of freedom, or establish chirality
at the level of relativistic fields.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Reed Dial Pastry
section columns
-- General frame observation, so no assertion of nonsingularity of the
-- kinetic restriction or constant rank of the overlap projector.
variable {I:Type*}[LinearOrder I][Fintype I]{D P:Op I}
private lemma columnChem (F S : Finset I) (K' : D*P=cutM F * P)
    (v:UNI I)(w:P=twist v (cutM S)) :
    chemical v.val F S=chemical (D*v.val) F S := by
  have hw: P*v.val=v.val*cutM S:=by rw [w]; exact twist_product ..
  have h: D*v.val*cutM S=cutM F*v.val*cutM S:=by rw [mul_assoc,mul_assoc,←hw,←mul_assoc,←mul_assoc,K'] -- watch
  have hp(i j:I)(x:i∈F)(y:j∈S): (D*v.val) i j=v.val i j:= by
    have p:= Matrix.ext_iff.mpr h i j
    simp only [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul, if_pos x, if_pos y,one_mul,mul_one] at p; exact p
  unfold chemical; congr 1; refine Finset.sum_congr rfl fun a x=>?_
  congr 1; exact Finset.sum_congr rfl fun i y=> by rw [hp a i x y]

-- the same z multiplies ALL Grassmann responses (at this gauge and in this frame)
private lemma matrix_phase (F S:Finset I)(K' : D*P=cutM F * P)
    (bra ket:Wave I) (z:Sea (cutM F) bra) (t: Sea P ket)
    (v:UNI I)(w:P=twist v (cutM S)) :
    ∃ q:ℂ, ‖q‖=1 ∧ ∀ x:FC I, Plain x→ inner ℂ bra (acts ((think F).eval x) ket)=
      q * zap F S ((tube S v.val).eval ((syms F).eval x)* exp (chemical (D*v.val) F S)) := by
  let U:=bra.ofLp F; let X:=inner ℂ (wedge v.val S) ket
  have hb:bra= U • basisKet F := z.1.symm.trans (by rw [Fock.cutLine,cut_oneAct])
  have hk:ket= X • wedge v.val S := t.1.symm.trans (by rw [w,act_twistLine])
  have hU: ‖U‖=1:=by have he:=z.2; rw [hb,norm_smul] at he; simpa [basisKet] using he
  have hX: ‖X‖=1:=by have he:=t.2; rw [hk,norm_smul,wedge_norm v S] at he; simpa only [mul_one] using he
  have he:=columnChem F S K' v w
  refine ⟨star U*X, by rw [norm_mul,norm_star,hU,hX,mul_one],?_⟩
  intro x y
  rw [←he]
  change _= _*spell (syms F) v.val F S x
  rw [Reed.moment v.val F S x y,hb,hk,map_smul,inner_smul_left,inner_smul_right,mul_assoc]; rfl
end columns

-- Apply to the literal top of Y independently of any claims about other regulator
-- laws. Keep spatial and time offsets from the FiniteGaugeData cut.
section wire
variable (i k:ℕ)(U:Pane (side Y i (Y.uv k)))
local notation "m"=>Vale.mesh (Y.ir i) Λ.R.L (Y.uv k)
local notation "nP" => side Y i (Y.uv k)
local notation "L"=>Single (side Y i (Y.uv k))
local notation "M"=> (helix (side Y i (Y.uv k))).symm
local notation "P" U:max=> spar Λ.K.j babyM U
local notation "W" U:max=> frame SU.matter (Cube.links U) (anticut nP)
local notation "D₀" U:max=> portW M (W U).overlap
local notation "R" => Tset (side Y i (Y.uv k))
local notation "β"=> (((Y.voyage i).X (Y.uv k)).gram (Y.uv k)).beta
variable (h: flags (Y.meter.a (Y.uv k)).threshold U=∅)
include h
lemma safeCutoff : Safe (frame SU.matter (Cube.links U) (anticut (side Y i (Y.uv k)))).H := by
  let z : Orbit (side Y i (Y.uv k)) := (U,Classical.arbitrary _)
  let A:= Y.history i k
  let f:=(Y.voyage i).CapeT (Y.uv k)
  have p:= A.roof (Y.uv k)
  have ex : f z=U:= Vale.Grace.Robes.solar z _ p.paid (Y.meter.a _) (A.pole _) h
  have hx : Guard U Λ.d:= ex ▸ ((p.paid.paid z).shrink Λ.J.hr.le)
  exact Phase.wiel_ok _ Λ.U.baseY hx

lemma exponent_column : (D₀ U) * (P U)=cutM (Tset (side Y i (Y.uv k))) * (P U) := by
  obtain ⟨v,p⟩:= Y.equity i k U h
  rw [v,←touchP]
  -- portW is reindexing of both matrices preserving composition
  have e : (W U).overlap * projector (W U).H = cutM (upperP _) * projector (W U).H := by
    rw [← Reed.plus_joint (Cube.links U) (anticut nP)]; exact (WilsonFrame.overlap_action _ (safeCutoff Y i k U h))
  let F:= love (side Y i (Y.uv k))
  change F _ * F _= F _ * F _
  rw [←map_mul, ←map_mul,e]

lemma occupied_band : IsStarProjection (spar Λ.K.j babyM U) := (Y.equity i k U h).1.symm ▸ carts_p M ((safeCutoff Y i k U h).projection)
lemma anyFrame : ∃ (v:UNI (Single (side Y i (Y.uv k))))(S:Finset (Single (side Y i (Y.uv k)))), spar Λ.K.j babyM U=twist v (cutM S) :=
  spot_projection _ (occupied_band Y i k U h)

-- This is the microscopic integrand after the physical identification. Includes
-- pointwise real-weight factor in exactly the FiniteGaugeData convention.
lemma action_at (v:UNI (Single nP))(S:Finset (Single nP))(p:(P U)=twist v (cutM S)) :
  ∃ c:ℂ, ‖c‖=1 ∧ ∀ (x:FC L) (A:Evaluation (side Y i (Y.uv k))),
    Plain x → A U=(think (Tset (side Y i (Y.uv k)))).eval x→
    bareAmplitude Y i k A U = Complex.exp (-(((((Y.voyage i).X (Y.uv k)).gram (Y.uv k)).beta*basicP Λ.K.top.clip U:ℝ):ℂ)) * c *
      zap (Tset (side Y i (Y.uv k))) S
        ((tube S v.val).eval ((syms R).eval x)* exp (chemical ((D₀ U)*v.val) R S)):=by
  obtain ⟨c,w,q⟩:= matrix_phase _ _ (exponent_column Y i k U h) (mateK nP) _ ((touchP nP) ▸ tickB nP) ((Y.equity i k U h).2) v p
  refine ⟨c,w,fun x A e a=>?_⟩
  unfold bareAmplitude Vale.capP; rw [Set.indicator_of_mem (show U∈{V:Pane nP| flags (Y.meter.a (Y.uv k)).threshold V=∅} from h),a,map_smul,inner_smul_right, q x e]; ring

omit h
open ExTwo
-- explicit letter sign and generation matrix. not renaming 3 independent connections!
lemma microscopic_letter (x:Site nP)(a:SpinIdx)(g:Fin 3)(t: SU.Ten ⊕ SU.F) :
    (think (Tset nP)).term ((x,a),g,t)= if a∈plusHalf then Fock.put ((x,a),g,t) else -Fock.takeF ((x,a),g,t) := by
  change (if _ then _ else _)=_; simp only [Window.mem_Tset]
lemma microscopic_multiplet (v:SU.E) :
    (SU.matter v).val=(1:Op (Fin 3)) ⊗ₖ Join.both (wedgeOp (SU.fund v)) (cc (SU.fund v)) := rfl

private lemma inverseWriter (S : Finset (Single nP)) :
    ∃ T : FC L →L[ℂ] FC L,
      (∀ x,Absorb S (T x)) ∧ ∀ x, Fine R S false x → (think R).eval (T x) = x:= by
  let F : Submodule ℂ (FC L) := {
    carrier := {x|Absorb S x}
    zero_mem' := Absorb.zero
    add_mem' := fun h p=> Absorb.sum h p
    smul_mem' := fun c _ h=> Absorb.scale h c }
  let E := (think R).eval.comp F.subtype
  let A:= E.range
  obtain ⟨G,g⟩ := LinearMap.exists_rightInverse_of_surjective E.rangeRestrict E.range_rangeRestrict
  obtain ⟨B,w⟩:= Submodule.exists_isCompl A
  let Q:= A.projectionOnto B w
  let V:=(F.subtype.comp G).comp Q
  refine ⟨LinearMap.toContinuousLinearMap V,fun x=> (G (Q x)).property,?_⟩
  intro x v; obtain ⟨y,u,h⟩:= v.writer; let X:A:=⟨x, ⟨⟨y,u⟩,h.symm⟩⟩
  change E (G (Q X.val))=X.val
  rw [show Q X.val=X from Submodule.projectionOnto_apply_left ..]
  exact congrArg Subtype.val (LinearMap.congr_fun g X)

/-- Choose the formal Grassmann insertions as Borel functions of just the
one local gauge region; the lemma `action_at` computes their physical
read including in exceptional rank sectors. (No scalar continuity claimed.) -/
lemma atCutoff_script {n:ℕ}{a:Set ℕ}{V:Set RSpace}{x:Altitude.Cloud (Dome (tent Y H))}{b:Bool}
    (q: x∈PhaseChoice.circum Λ l (tent Y H) b V (a ∩ Set.Iic n))(p: Pay Y n i k):
    ∃ S:Finset Cover, SupportedPhysically Λ l (Y.uv k) S V ∧
       AtSupport false (Satin.region S nP) (toMark (atCutoff Y H i k x)) ∧
       covariant (toMark (atCutoff Y H i k x)) ∧
       ∃ w:Pane nP → FC L, Envelope w ∧
          Lattice.LocalOn (Satin.region S nP) w ∧
          ∀ z:Pane nP, Absorb (modesIn nP (Satin.region S nP)) (w z) ∧ Plain (w z) ∧
            (atCutoff Y H i k x) z=(think R).eval (w z):=by
  obtain ⟨S,t,f⟩:= top_location Y H i k n q p
  obtain ⟨Fg,u,e⟩:= inverseWriter Y i k (modesIn nP (Satin.region S nP))
  let A(z:Pane nP):=atCutoff Y H i k x z
  let w:=Fg ∘ A
  have ht : Envelope A:= Env.along (g:=fun U:Pane nP=>(U,U)) f.env (measurable_id.prodMk measurable_id)
  exact ⟨S,t,f,colorAtCutoff Y H i k n q p,w,Girt.pole_w A Fg Fg.continuous ht,
    fun x y h=> congrArg Fg (f.dep (x,x) (y,y) h h),fun z=> ⟨u _, (u _).packs (Finset.subset_univ _),(e _ (f.allV (z,z))).symm⟩⟩
end wire
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
