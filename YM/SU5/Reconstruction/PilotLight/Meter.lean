import YM.SU5.Reconstruction.Cashier.Factual
/-! `the construction notes` (mathematical plan). Part 1: Lode full permission -- ZERO in the oriented
arena itself (not just the commuting compression). Thus gauge-charge comparison with any of these
probes in such an aperture gets literal zero in this reconstruction.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
open SatinVerification Tapestry PhaseChoice
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(j:Axis) (C:Arena Y H G.history.circuit j 0 false)
  (S:Finset Cover)(s w:ℕ)(t:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
local notation "R₀"=>render S (tent Y H)
local notation "B"=>allBox Y H V G j S s C w t hw
local notation "Q"=>Ark.Ht Y H G.history.circuit j 0 false C
open CF.Pannier.Chancel
open Selected
open Chambers
section root
private def meterValue (f: Family (tent Y H)) : (Q).Op:= if p:InTest K true S false f then allBox Y H V G j S s C w t hw (fabric S K p) else 0
local notation "M"=>meterValue Y H V G j C S s w t hw
private lemma metered (x:Swatch S):M ((R₀) x) = (B) x:=by rw [meterValue,dif_pos (texture ..),fabric_render]
private lemma circularGauge (f F: Family (tent Y H)) (v:InTest K true S false f)(p:InTest K true S false F)(g:Cover → SU.E)(q:Circular S g f F): M f=M F:=by
 obtain ⟨x,rfl⟩:= rendered S K v; obtain ⟨y,rfl⟩:=rendered S K p
 rw [metered,metered]; exact stance_color Y H V G j false C S s w hw (toEntry Y H j false S s w t (allHues Y H S x)) (toEntry Y H j false S s w t (allHues Y H S y)) v p t q

lemma site_annuls {n : ℕ} (a:Fin n → Cover)(p:Injective a)(z:Window.Family)(f: Swatch S)(e:(render S K) f∈ Lode K z a S): B f=0:=by
 let ψ:= E s; have hp:Scopes K S ψ:= Papal.ledgerRule Y H V S s -- tune params
 ext1 q; apply ext_inner_left ℂ; intro x
 let A(t':Family K):= inner ℂ x ((M t') q); let c:= 1-A 1; let P(t':Family K):= A t'+ c*ψ t'
 have ht:Scopes K S P:= by
    constructor
    · unfold P c; rw [hp.unit]; ring
    · intro f g p q'
      obtain ⟨k,rfl⟩:=rendered S K p; obtain ⟨l,rfl⟩:=rendered S K q'; unfold P A; rw [hp.plus_v _ _ p q',← map_add (render S K),metered,metered,metered,map_add,ContinuousLinearMap.add_apply,inner_add_right]; ring
    · intro f p b; obtain ⟨k,rfl⟩:=rendered S K p; unfold P A; rw [hp.scale _ p,←map_smul (render S K),metered,metered,map_smul,ContinuousLinearMap.smul_apply,inner_smul_right]; simp only [smul_eq_mul]; ring
    intro b f F p F' i; unfold P A; rw [circularGauge Y H V G j C S s w t hw f F p F' b i,hp.gauge b _ _ p F' i]
 have he:=ht.footprint p e; change inner ℂ x ((B f) q)=inner ℂ x 0; unfold P A at he; rwa [metered,hp.footprint p e,mul_zero,add_zero,←inner_zero_right (𝕜:=ℂ) x] at he -- gate

include t in
lemma pocket_cold {n:ℕ}{a: Fin n → Cover} (p:Injective a){z:Window.Family} {f : Family K} (e:f∈Lode K z a S) (x: Entry Y H s j false w)(g:x.val.val=f): boxOp Y H V s G.history G.clipped j false C w x hw=0:=by
 have hx:InTest K true S false f:=(Lode_test e).widen; obtain ⟨F,u'⟩:= rendered S K hx
 rw [box_chart Y H V G j S s C w t hw F (g.trans u'.symm)]
 exact site_annuls Y H V G j C S s w t hw a p z _ (u'.symm ▸ e)
end root
open SlabMark MeshClock
variable (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
include t hw
lemma vanishesLode {n:ℕ} {a:Fin n→ Cover} (p:Injective a){f:Dome K} {z:Window.Family} (h:f.val∈ Lode K z a S):
    Follows Y H V G j C χ (ticket Y H G s f) (notch (timeMesh Λ) s w) 0 := by
 let H' : f∈insideAt Λ l K false (strip j 0 (whenly (timeMesh Λ) s w:ℝ)) s:= (mem_insideAt ..).2 ⟨⟨S,(Lode_test h).widen,(strip_seats ..).2 t⟩, nofun⟩
 let g:= startOp Y H j s w f H'
 have h': entrance Y H V s G.history G.clipped j false C g hw = 0 := Subtype.ext (pocket_cold Y H V G j C S s w t hw p h g rfl)
 have hx:= arrangement Y H V G j C χ s w g hw
 rw [h',map_zero] at hx; exact hx
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.site_annuls
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.vanishesLode
