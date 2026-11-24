import YM.SU5.Assay.Jaw
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
/-!
 `Brim t m w f`: colored stamp fitted after recentering to
 interval `[m,m+w]` in ticks. No beam/charge claims. Its currency
 `costing` is represented box on raw coloration space (before compression).
 All pricing data already in Spine at x.
-/
def Brim (m:ℤ)(w:ℕ)(f:P.Test):Prop:= P.BEntry j w (σ (-m) f) ∧ f∈T
def costing (m:ℤ)(w:ℕ)(f:P.Test): X:=μ w (σ (-m) f)
local notation "β"=>P.costing j x t
variable {P j}{f g:P.Test}{w v:ℕ}{m n:ℤ}
namespace Brim
lemma pigment (h:P.Brim j m w f) : σ (-m) f∈T:=P.shifts_keep j (-m) h.2
lemma price (h:P.Brim j m w f):inner ℂ (Vac) (β m w f (Vac)) = P.singleState j t x f:=by
 rw [costing,seenBox_scalar t x h.1 h.pigment,P.slide_single]
lemma zero (P:Spine)(j:Axis)(m:ℤ)(p:0<w): P.Brim j m w 0:=by
 refine ⟨?_,zero_mem _⟩;rw [map_zero];exact BEntry.zero P j p
lemma price_zero (m:ℤ)(h:0<w):β m w 0=0:=by rw [costing,map_zero,seenBox_zero t x h]
lemma smul (h:P.Brim j m w f)(z:ℂ):P.Brim j m w (z•f):=by
 refine ⟨?_,(T).smul_mem h.2 z⟩
 rw [map_smul];exact h.1.smul z
lemma add (h:P.Brim j m w f)(p:P.Brim j m w g):P.Brim j m w (f+g):=by
 refine ⟨?_,(T).add_mem h.2 p.2⟩
 rw [map_add];exact h.1.add p.1
lemma price_smul (h:P.Brim j m w f)(z:ℂ):β m w (z•f)=z•β m w f:=by
 unfold costing;rw [map_smul]; exact seenBox_smul t x h.1 h.pigment z
lemma price_add (h:P.Brim j m w f)(p:P.Brim j m w g):β m w (f+g)=β m w f+β m w g:=by
 unfold costing;rw [map_add];exact seenBox_add t x h.1 p.1 h.pigment p.pigment
lemma stretch (h:P.Brim j m w f)(d:n ≤ m)(u:m+w ≤ n+v):
 P.Brim j n v f ∧ β n v f=(U).sand (β m w f) (τ m-τ n) (τ (n+v)-τ (m+w)):=by
 let a:ℕ:=(m-n).toNat; let b:ℕ:=(n+v-(m+w)).toNat
 have ha:(a:ℤ)=m-n:=Int.toNat_of_nonneg (by omega)
 have hb:(b:ℤ)=n+v-(m+w):=Int.toNat_of_nonneg (by omega)
 have hW:a+w+b=v:=by omega
 have g:σ (-n) f=σ a (σ (-m) f):=by rw [shifts_sum,ha,show m-n + -m= -n by abel]
 unfold Brim costing; rw [g]; have he:=h.1.pad a b; rw [hW] at he
 refine ⟨⟨he,h.2⟩,?_⟩
 have q:= seenBox_pad t x h.1 h.pigment a b; rw [hW] at q; rw [q]
 have ga:=congrArg (τ) ha;have gb:=congrArg (τ) hb
 rw [P.tock_sub,P.tock_when] at ga gb; unfold sand wax
 rw [←ga,←gb,Real.toNNReal_coe,Real.toNNReal_coe]

private lemma seen_con (p:P.BEntry j w f)(q:P.BEntry j v g)(a:f∈T)(b:g∈T):
 μ (w+v) (f*σ w g)=μ w f*μ v g:=by
 unfold seenBox;rw [←map_mul];apply congrArg Φ;refine Subtype.ext (Subtype.ext ?_)
 change (P.doorBox _ _ _ _).val.val=(P.doorBox _ _ _ _).val.val*(P.doorBox _ _ _ _).val.val
 rw [doorBox_val t p a,doorBox_val t q b,doorBox_val t (p.concat q) ((T).mul_mem a (P.shifts_keep j _ b))];exact meanBox_concat t p q
private lemma straddle : σ (-m) (f*g)=σ (-m) f*σ w (σ (-(m+w)) g):=by rw [map_mul,shifts_sum,show (w:ℤ)+(-(m+w))= -m by abel]
lemma adjoin (p:P.Brim j m w f)(q:P.Brim j (m+w) v g):P.Brim j m (w+v) (f*g):=by
 refine ⟨?_,(T).mul_mem p.2 q.2⟩
 rw [straddle (w:=w)];exact p.1.concat q.1
lemma price_adjoin (p:P.Brim j m w f)(q:P.Brim j (m+w) v g):β m (w+v) (f*g)= β m w f*β (m+w) v g:=by
 unfold costing;rw [straddle (w:=w)];exact seen_con x t p.1 q.1 p.pigment q.pigment
lemma stitch (p:P.Brim j m w f)(q:P.Brim j n v g)(d:m+w ≤ n):
 ∃r:ℕ,m+r=n+v ∧ P.Brim j m r (f*g) ∧ β m r (f*g)=β m w f*ℇ (τ n-τ (m+w))* β n v g:=by
 let b:ℕ:= (n-m).toNat; have hb:(b:ℤ)=n-m:=Int.toNat_of_nonneg (by omega)
 have hn:m+b=n:=by omega
 obtain ⟨u,z⟩:=p.stretch x t (le_refl _) (v:=b) (by omega)
 have q':P.Brim j (m+b) v g:=by rwa [hn]
 refine ⟨_,?_,u.adjoin q',?_⟩
 · omega
 rw [price_adjoin x t u q',z,sub_self,hn];unfold sand;rw [wax_zero,one_mul]
end Brim
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
