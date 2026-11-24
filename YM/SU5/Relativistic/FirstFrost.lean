import YM.SU5.Relativistic.LevelCarn
import YM.SU5.Relativistic.Hereafter
import YM.SU5.Relativistic.FirGreen
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "M" n:max=> cargoV Y H D G u t j s n
local notation "B₁" s:max=> creed Y H D G d j c x s

variable {b₀:ℕ}
noncomputable def endings (f:F₀): Dome (tent Y H):= ⟨_,(levied j K f f).scale Complex.I⟩
local notation "L₁" f:max=>pinhole D₀ s (endings Y H j f)
local notation "pd" w:max=> vistaFinish Y H w D
variable (N:Future Y H j b₀)
noncomputable def sunnyF (N:Future Y H j b₀) (f:F₀) : F₀:= by
 let v:=Future.emit Y H j N; refine ⟨f.val*v.val,?_⟩; obtain ⟨S,h,z⟩:=hutSpec j K f; let W:= Future.opening Y H j N; have hp:InTest K true W false v.val:=Future.emit_extent Y H j N
 have hg: Tower.region j 0 (K).ℓ W:=by
    intro i w; refine le_trans ?_ (Future.op_far Y H j N i w); have he:0 ≤ ruler Λ.block*(Future.wait Y H j N:ℤ) := mul_nonneg (ruler_gene _).le (by positivity); linarith
 exact ⟨S∪W,(h.mono (subset_union_left (s₂:=W))).mul (hp.mono subset_union_right),fun i k=> (mem_union.mp k).elim (z i) (hg i)⟩
local notation "Sa"=> sunnyF Y H j
lemma sunnyMoves (x:F₀)(n:ℕ) : Sa (N.reach Y H j n) (α n x)=α n (Sa N x):=by
 apply Subtype.ext
 change relocate K j _ x.val*(Future.emit Y H j _).val=relocate K j _ (x.val * (Future.emit Y H j N).val)
 rw [Future.reach_dub, timed_apply,relocate_mul]
-- tune
local notation "r" => (N.t - s)
include D G t
lemma old_card (f:F₀)(h:s≤N.t) : vistaTake Y H D ((L₁ f) * Future.boundary Y H j N)=
    unB Y H V j N.t (Sa N ((M r) f)) (Sa N ((M r) f)):=by
   let L':= L₁ f; let X:=Sa N ((M r) f); let y:=Future.emit Y H j N
   have he:s+r=N.t:=by omega
   have hl:L'∈ shorter D₀ s:= short_pinhole s _
   have hv:L'∈ shorter D₀ N.t:= climbs D₀ h hl
   change vistaTake Y H D (L' * pinhole D₀ N.t (Future.kernelPath Y H j N))=_
   rw [vistaCall Y H N.t _ D ((shorter D₀ N.t).mul_mem hv (short_pinhole N.t _))]
   have hy: (pd N.t) (L'* (Future.boundary Y H j N))= (pd N.t) L' * Future.kernelPath Y H j N:= Decking.last (vistaDressing Y H D) (auxiliaryPad K) L' N.t hv _
   let W:=M r
   have hg: ((pd N.t) L').val=stream Y H G.refine s r (Complex.I • (mirror K j 0 f.val*f.val)):=by
      have hp:(pd s) L'=endings Y H j f:= (by unfold L' vistaFinish; rw [Decking.outcrop]; rfl)
      exact ((congrArg (fun v=> ((pd v) L').val) he).symm.trans (finish_upwards Y H D G s hl r)).trans (congrArg (fun x':D₀=> stream Y H G.refine s r x'.val) hp)
   change E N.t ((pd N.t) (L'*(Future.boundary Y H j N))).val = E N.t (Complex.I • (mirror K j 0 X.val * X.val))
   rw [hy]; change E N.t (((pd N.t) L').val*(mirror K j 0 y.val*y.val))=_
   have hx0:X.val=(W f).val*y.val:= rfl
   have ht:InTest K true _ true (W f).val:=(hutSpec j K (W f)).choose_spec.1
   have hf: (W f).val * mirror K j 0 y.val =mirror K j 0 y.val * (W f).val:=by
      simpa only [Sector.grainB,Bool.and_false,Bool.false_eq_true,ite_false,one_smul,y] using signMark K ht (axial K j 0 (Future.emit_extent Y H j N))
   rw [hg,block_step Y H D G u t j s r, hx0,mirror_times,Algebra.smul_mul_assoc]; change E N.t _ = E N.t _; apply congrArg (E N.t); simp only [mul_assoc] ; rw [show (M r)=W from rfl,←mul_assoc (W f).val,hf,mul_assoc]

include d x
lemma halls (f:F₀) (e:ℕ): ‖(B₁ s) (α e f) (α e f)‖ ≤ ‖(B₁ s) f f‖:=by
 obtain ⟨Z,z⟩:= display_receives Y H V G.history G.clipped j false (c j)
 obtain ⟨y,a⟩:= z.onto.surjective (χ j); have a':Z.character y=χ j:=a
 let X:= SameCharacter.resident Y H V G j false (c j) (Z.character y)
 have he (f:F₀): (B₁ s) f f= onDrawing Y H V G D j c X (L₁ f):=by
    have hp:= (levied j K f f).scale Complex.I
    let u':Marks K false:=⟨_,hp,nofun⟩
    rw [chorded Y H D G u t]; change ψ s u'.val =_; rw [← selected_here Y H D G d j c x s u']
    unfold X; rw [a']
    have ht:= costs_pinhole Y H D G j c (χ j) s (endings Y H j f)
    change (φ s) u'=_; refine Eq.trans ?_ ht.symm; rw [show (endings Y H j f).val=u'.val from rfl,evaluates Y H V G j c (SameCharacter.resident Y H V G j false (c j) (χ j)) s u',SameCharacter.sameReading]
 let g:= α e f
 obtain ⟨G₀,p,z⟩:= pushes_go Y H D G j c Z z y
 let k(i:ℕ):=Λ₀^((G₀ i).t-s)*e
 rw [he f,show α e f=g from rfl,he g]
 apply le_of_tendsto_of_tendsto ((z k).focus _ (curve.mpr ⟨s,short_pinhole s (endings Y H j g)⟩)).norm (p.focus _ (curve.mpr ⟨s,short_pinhole s (endings Y H j f)⟩)).norm
 filter_upwards [eventually_ge_atTop s] with i si
 let N:=G₀ i; let w:=Future.reach Y H j N (k i); have hp:s≤ N.t:=si.trans N.arrival
 change ‖vistaTake Y H D ((L₁ g)*Future.boundary Y H j w)‖≤ ‖vistaTake Y H D ((L₁ f)*Future.boundary Y H j N)‖
 rw [old_card Y H D G u t j s w g hp, old_card Y H D G u t j s N f hp]
 change ‖unB Y H V j N.t (Sa w ((M (N.t-s)) (α e f))) (Sa w ((M (N.t-s)) (α e f)))‖≤_
 have ht: (M (N.t-s)) (α e f)=α (k i) ((M (N.t-s)) f):= powers Y H D G u t j s (N.t-s) f e
 rw [ht,show w=_ from (rfl : w=Future.reach Y H j N (k i)),sunnyMoves]; exact unB_contract ..
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.halls
