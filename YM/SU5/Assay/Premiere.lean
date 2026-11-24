import YM.SU5.Assay.Drive
import YM.SU5.Assay.Interval
import YM.SU5.Assay.ArchivedBalcony
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
open Etch

variable (j:Axis)(w:ℕ)(σ:Cover)(hw:0<w)(z:σ j=0)
local notation "N₀"=>slideN Y s w
variable {S:Finset Cover}{f:Family (tent Y H)}(g:ℕ→Family (tent Y H))
  (t:BQueue S g f)(u:House (tent Y H) w σ 0 S)

/-- Terminal checkers with *sharp* reading. C constant per copy.
 A further pricing subsequence with the same D,E can be used. -/
def Premiere (c:ℝ):Prop:=∀ᶠ e:ℕ in atTop,Mosaic w σ (N₀ (π e)) (g e) c
   (sharp Y H s (π e) (ζ e))

local notation "sold" =>Premiere (i:=i) (k:=k) (a:=a) (b:=b) Y H s w σ g

include V Q hw t u z
lemma premiereMatinee (c d:ℝ)(hc:0<c)(hd:c<d)(v:sold c):
    Matinee (i:=i) (k:=k) (a:=a) (b:=b) Y H s j w g d:=by
 obtain ⟨A,hA,_,hp⟩:=t.bdd
 filter_upwards [hp,screenFlash Y H V s Q A c d hA hc hd,v,framing Y H V s Q w hw,Q.finance s] with e h hf y h₀ hg
 intro r i
 let a:=collector Y H (π e) (ζ e) hg.depth s
 obtain ⟨hr,gle,ht⟩:=h₀
 have gas:2*(ruler (K).B*w*r)≤((((K).c (m (π e) s)).val:ℕ):ℤ):=by rw [side_register]; exact gle
 have hw':0≤ (w:ℤ):=by positivity
 have hm:Mosaic w σ r (g e) d (fun x:Family _=>a (x (m (π e) s))):=by
   intro lo hi n b e' G P
   have h₁ : 0<n:=by have z:0< (4*r)^4:=(by positivity); have a:=z.trans_le b.1; omega
   have h₂:n≤ (2*(T₀ (π e) s).val)^4:=le_trans b.2 (by gcongr)
   obtain ⟨⟨S,hT,_⟩,hP⟩:= P.receives _ _ _ hw' (t.whereTo e) u h
   have hx:=(hf n h₁ h₂ G (aux_test hT) hP).1 (y lo hi n b e' G P)
   unfold hot at hx; rw [dif_pos hg.depth] at hx; exact hx
 unfold hot; rw [dif_pos hg.depth]
 exact bannerView w σ (boxprice Y H _ _ _ s hg.fire hg.enters) hw' (t.whereTo e) u h r gas j z hr d (hc.trans hd).le hm i

omit V Q hw t
lemma entryHouse:Between (tent Y H) j 0 (ruler (K).B*w) S:=by
 have h:=u j; unfold runnel at h; simpa [z] using h
include V Q hw t
lemma premiereTurn (c d:ℝ)(hc:0<c)(hd:c<d)(v:sold c): Turnstile (i:=i) (k:=k) (a:=a) (b:=b) Y H s j w S g (d^2):=by
 have hx:Between (tent Y H) j 0 (ruler Λ.block*w) S:=entryHouse Y H j w σ z u
 let q:=(c+d)/2; have ht:c<q:=by unfold q; linarith
 have he:q<d:=by unfold q; linarith
 exact matineeTurn Y H V s Q j w hx g t hw q d (hc.trans ht) he (premiereMatinee Y H V s Q j w σ hw z g t u c q hc ht v)

variable {a' b':ℕ→ℕ}(G:Coherent (i:=i) (k:=k) (E:=E) Y H D a' b')(Qt:Clipped Y H (i∘a') (k∘b'))
variable (strict:Bool)(C:Arena Y H G.circuit j 0 strict)(F:Entry Y H s j strict w)
omit t

/-- Terminal checkers pay operator norm of aligned slot on the limiting prescription.
 Each hypothesis itself with positive arbitrarily small slack per copy; if purchased
 without that slack, use price monotonicity (nonnegative). Q prices; G situates
 the same prescription. Even if sharp prices use moving marks on the path. -/
theorem premiereBox (h:BQueue S g F.val.val)(d:ℝ)(hd:0≤d)(y:∀ q:ℝ,d<q→sold q):
   ‖boxOp Y H V s G Qt j strict C w F hw‖≤d:=by
 by_contra! hh
 obtain ⟨a,hq,t⟩:=exists_between hh
 obtain ⟨q,p₁,p₂⟩:=exists_between hq
 have hx:Between (tent Y H) j 0 (ruler Λ.block*w) S:=entryHouse Y H j w σ z u
 have pl:=premiereTurn Y H V s Q j w σ hw z g h u q a (hd.trans_lt p₁) p₂ (y q p₁)
 exact (not_le.mpr t) (boxTurn Y H V s G j strict C w F Qt hw Q S hx g h a (hd.trans_lt hq) pl)
end YM.CF.Buffered.Afterglow.Tower.SlabMark
