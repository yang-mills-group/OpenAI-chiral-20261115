import YM.SU5.Assay.Grips
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
variable (t:ℕ)
local notation "Φ"=>P.colorSpace j x
local notation "μ"=>P.seenBox j x t
local notation "σ"=>P.shifts j
local notation "τ"=>P.tock t
local notation "T"=>enclave P.calibration
local notation "ℇ"=>(P.physicalEnergy j x).wax
local notation "β"=>P.costing j x t
local notation "𝕤"=>P.Sill j x t
local notation "𝔤"=>P.Grips j x t
variable {P j x t}{a b c d:ℝ}{f g:P.Test}{A L:(P.ColorHil j x).Op}{m n:ℤ}{w v:ℕ}
lemma Brim.sill (x:P.Spectrum0 j)(t:ℕ)(p:P.Brim j m w f):
 P.Sill j x t (P.tock t m) (P.tock t (m+w)) f (P.costing j x t m w f) m w:=
 ⟨le_rfl,le_rfl,p,by simp only [sub_self,sand,wax_zero,one_mul,mul_one]⟩
lemma Grips.price (h:𝔤 a b f A):inner ℂ (Vac) (A (Vac))= P.singleState j t x f:=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,p,q,h,rfl⟩
 · simp only [map_zero,_root_.zero_apply,inner_zero_right]
 change inner ℂ (Vac) (ℇ _ (β m w f (ℇ _ (Vac))))=_
 unfold wax
 rw [←(U).swing,P.sector_hot,P.sector_hot,Brim.price x t h]
private lemma ham_wax {k y z u:ℝ}(p:y ≤ b)(q:b ≤ z):
 (U).sand A k (b-y) * (U).sand L (z-b) u =
 (U).sand (A * (U).wax (z-y) * L) k u:=by
 have t: _ = (U).wax (z-y) := ((U).wax_sq (sub_nonneg.mpr p) (sub_nonneg.mpr q)).trans
    (congrArg (U).wax (show b-y+(z-b)=z-y by abel))
 unfold sand
 rw [←t];simp only [mul_assoc]
lemma Grips.join (h:𝔤 a b f A)(k:𝔤 b c g L):𝔤 a c (f*g) (A*L):=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,p,q,h,rfl⟩; · rw [zero_mul,zero_mul];exact Grips.zero ..
 rcases k with ⟨rfl,rfl⟩|⟨n,v,d,e,k,rfl⟩; · rw [mul_zero,mul_zero];exact Grips.zero ..
 obtain ⟨r,z,l,jt⟩:=Brim.stitch x t h k ((P.tock_le t _ _).mp (q.trans d))
 exact Sill.grips (m:=m) (w:=r) ⟨p,(congrArg (τ) z).trans_le e,l,by rw [jt,z,ham_wax q d]⟩
lemma Grips.exact (h:𝔤 (τ m) (τ (m+w)) f A)(hw:0<w): P.Brim j m w f ∧ A=β m w f:=by
 suffices p:P.Brim j m w f by exact ⟨p,h.unique (Brim.sill x t p).grips⟩
 rcases h with ⟨rfl,rfl⟩|⟨n,v,p,q,l,rfl⟩
 · exact Brim.zero P j m hw
 exact (l.stretch x t ((P.tock_le t _ _).mp p) ((P.tock_le t _ _).mp q)).1
lemma Grips.corners (h:𝔤 a b f A)(p:τ m ≤ a)(q:b ≤ τ (m+w))(hw:0<w):
 P.Brim j m w f ∧ β m w f=(U).sand A (a-τ m) (τ (m+w)-b):=by
 obtain ⟨l,d⟩:= (h.outer p q).exact hw;exact ⟨l,d.symm⟩

/-! First wall present vacuum frame. -/
lemma tock_late (P:Spine)(t:ℕ)(m:ℤ)(b:ℝ):∃w:ℕ,0<w ∧ b ≤ P.tock t (m+w):=by
 let p:= P.macroStep_pos t
 let v:=P.tock t m
 obtain ⟨w,r⟩:=exists_nat_gt (max 0 ((b-v)/P.macroStep t))
 have d:(0:ℝ)<w:=(le_max_left ..).trans_lt r
 have e:= ((div_lt_iff₀ p).mp ((le_max_right ..).trans_lt r)).le
 refine ⟨w,by exact_mod_cast d,?_⟩
 rw [P.tock_add t,P.tock_price t (↑w:ℤ),Int.cast_natCast]; unfold v at e;linarith only [e]
lemma Brim.birth (x:P.Spectrum0 j)(t:ℕ)(p:P.Brim j m w f):
 ∃ k:P.birthF j t (σ (-m) f),P.viewF j x t k=P.costing j x t m w f (P.colorZero j x):=by
 have z:=p.1
 have q:P.voxTest j t (z.card t).val∈T:=p.pigment
 refine ⟨P.admitted_view j t _ q,Eq.symm ?_⟩
 rw [costing,seenBox_card t x (z.card t) z.pos q (f:=σ (-m) f) rfl];exact P.attended j x t z.pos (z.card t) q
lemma Grips.birth (h:𝔤 a b f A)(p:τ m ≤ a):
 ∃ k:P.birthF j t (σ (-m) f),P.viewF j x t k=ℇ (a-τ m) (A (Vac)):=by
 obtain ⟨w,c,e⟩:=P.tock_late t m b
 obtain ⟨u,g⟩:=h.corners p e c
 obtain ⟨k,v⟩:=Brim.birth x t u
 refine ⟨k,v.trans ?_⟩
 rw [g];change ℇ _ (A (ℇ _ (Vac))) = _; unfold wax;rw [P.sector_hot]
lemma Grips.present (h:𝔤 0 b f A):∃ k:P.birthF j t f, P.viewF j x t k=A (Vac):=by
 have q:= Grips.birth (m:=0) h (le_of_eq (P.tock_zero ..))
 rw [P.tock_zero,sub_self,wax_zero,neg_zero,P.shifts_zero] at q;exact q
lemma Grips.act (h:𝔤 a b f A)(p:τ m ≤ a)(q:b ≤ τ (m+w))(d:0<w)(u:P.birthF j t g):
 ∃k:P.birthF j t (σ (-m) f * σ w g), P.viewF j x t k=(U).sand A (a-τ m) (τ (m+w)-b) (P.viewF j x t u):=by
 obtain ⟨z,r⟩:=h.corners p q d
 have y:P.voxTest j t (z.1.card t).val∈T:=z.pigment
 obtain ⟨v,e⟩:=P.accepted_view j x t w d (z.1.card t) y u
 refine ⟨v,?_⟩
 rw [←r,costing,seenBox_card t x (z.1.card t) d y (f:=σ (-m) f) rfl];exact e.symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
