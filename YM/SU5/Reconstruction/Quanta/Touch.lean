import YM.SU5.Reconstruction.Quanta.Epicycles
import YM.SU5.FiniteGaugeData.Tower.Performed
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-! # Lift the actual POS witnesses even odd. Resolution keeps parity upon transfer. -/
open QuantaCore NorthTapes
namespace Garret
variable {g₀:Bool}{S Z:Finset Cover}{f g:Family (tent Y H)}
local notation "W" =>wingspan Λ l
local notation "B" => Λ.block
local notation "L"=>Λ.R.L.val

variable (a:Axis)(z:ℤ)
local notation "W₀" t:max=> volumeAround Λ l t
local notation "v₀" q:max =>((Λ.R.L.val:ℤ)^q*z)
local notation "Pm" z:max => poleForm K a z
variable {a₀ b:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q: Coherent (i:=i) (k:=k) (E:=E) Y H D a₀ b)
local notation "π₀" r:max=>i (a₀ r)
local notation "κ" r:max=>k (b r)
local notation "tr" r:max t:max S:max F:max=> train Y H s t (π₀ r) (κ r) S F
local notation "Qr" r:max g:max S:max f:max t:max=> quarry Y H s (π₀ r) (κ r) g S f t
local notation "Ft" k:max S:max g:max p:max=> InTest K true ((W₀ k) S) g p
local notation "hv" t:max m:max => ((tent Y H).c (momentm Y m t))

open Tapestry
section tone
variable {R:Calibration}{F F':Family R}
lemma orb {m:Side}(a:Tivoli S (R.c m))(f:InTest R true S g₀ F)(q:InTest R true S g₀ F')(u:F m=F' m) : F=F':=by
 obtain ⟨x,d⟩:=tokenC S R f; obtain ⟨y,e⟩:=tokenC S R q
 have r':x=y:=by
    funext p; apply Subtype.ext; funext z
    let n:=R.c m; let Zz:=replant S n z; let D: PairsC := Prod.map (onC n) (onC n) Zz
    have ht(u:Purse S): u.val D=u.val z:= u.property.locus D z (fun i hx _=>tail S n a.hosp _ i hx) (fun i hx _=>tail S n a.hosp _ i hx)
    rw [← ht (x _),← ht (y _),← charged_both S R m a x d Zz,← charged_both S R m a y e Zz,u] -- tune notation Z binder
 rw [d,e,r']
lemma onceCov {m:Side}(p:InTest R true S g₀ F)(a:Tivoli S (R.c m))(v:covariant (F m)): CovCover R F:=by
 change Tapestry.Neutral R F; apply (harmonicHere (S:=S)).2; intro T; obtain ⟨u,h,H⟩:= reColor T p
 obtain ⟨g,t⟩:= scoreTrace T a.hosp
 have he: F=u := orb a p h (funext fun x=> (twist (Fock.quantU (tradew _ g))).injective ((v g x).symm.trans (H m g t x)))
 rwa [←he] at H
-- gauge identity acts trivially on ALL. needed when polling.
lemma anywhereOne (p:InTest R true S g₀ F): Circular S (1:Cover→ SU.E) F F:=by
 obtain ⟨m,h⟩ := (Buffered.separates R (Satin.tips S)).exists
 obtain ⟨F',q,t⟩ := reColor (1:Cover → SU.E) p
 have he (x) := t m (1:Seat (R.c m) → SU.E) (fun _ _ => rfl) x
 have heq : F = F' := orb ⟨⟨h⟩⟩ p q (funext fun x =>
    (twist (Fock.quantU (tradew _ (1:Seat (R.c m) → SU.E)))).injective ((oneHarmony (F m) x).symm.trans (he x)))
 rwa [←heq] at t
end tone
-- extension on living branch preserves each gauge-certified observer even if odd
lemma native_pick (m k:ℕ)(e:legalAt Y s m k)(hg:Tivoli (W S) ((tent Y H).c (momentm Y m (s+1))))(hp:InTest (tent Y H) true S g₀ f) (h:CovCover K f) : CovCover (tent Y H) (pick Y H s m k g₀ S f):=by
 let U:=pick Y H s m k g₀ S f
 obtain ⟨H₁,H₂⟩:=lamp_jump Y H s m k e hp hg
 apply onceCov H₁ hg
 unfold distribute at H₂
 suffices q:covariant (aboveD Y H s m k f) by
    rw [← H₂] at q; let p:= terrain Y H (Y.ir m) (s+1); have ht:=castV p.symm q; rw [Tower.reverse] at ht; exact ht
 let g:= (Vale.apt (Y.ir m) Λ.block Λ.R.L s); let a:=((Y.voyage m).X (Y.uv k)); let K₁:=steps Λ.V (Y.ir m) Λ.block (Y.uv k); let p:= (fullness Y m k e.1).cap_grant
 obtain ⟨j⟩:= p.grant s e.2; obtain ⟨w,v,i,F0,u⟩:= j.cap
 exact gauge_pushed g Λ.K.j (Journey.aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) Λ.R.odd_side (a.gram (s+1)).J.M (a.wave s) (K₁ s) Chi.canonical (a.gram (s+1)).beta Λ.J.d ((Y.voyage m).CapeT s) (p.aligned s e.2) (p.branch s e.2) j.legal.1 j.legal.2 (locates Y H s m hp) (castV (terrain Y H (Y.ir m) s) (h _)) F0
where castV {x y:Side}(h:x=y){f:Mark x}(p:covariant f):covariant (Tower.ship h f):=by subst x; exact p
include V Q
variable (S)
lemma voiceArc (t:ℕ) : ∀ᶠ r in atTop,∀ u:ℕ, u≤t→∀ (f:Family (tent Y H)) (g₀: Bool), InTest K true S g₀ f→ CovCover (tent Y H) f→ CovCover (tent Y H) (Qr r g₀ S f u):=by
 have p:∀ᶠ r in atTop, ∀ u∈ Finset.range t, Tivoli ((W₀ (u+1)) S) ((tent Y H).c (momentm Y (π₀ r) ((s+u)+1))):=by
    rw [Finset.eventually_all]; intro u _; exact (((V.pick.grow_i.comp Q.growsA).tendsto_atTop).eventually (turning Y H ((s+u)+1) ((W₀ (u+1)) S)))
 filter_upwards [living Y H V s S Q t, p,certified Y H V s S Q t] with r c h a u v f b e y; induction u with
 | zero=>exact y
 | succ u ih=>
   have hx:u<t:=by omega
   have hz:= c u hx.le f b e
   exact native_pick Y H (s+u) (π₀ r) (κ r) ((a u hx b _ hz).1) (h u (Finset.mem_range.mpr hx)) hz (ih hx.le)
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.anywhereOne
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.voiceArc
