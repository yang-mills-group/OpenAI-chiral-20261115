import YM.SU5.FiniteGaugeData.Marked.Variation.Library
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Sing
/-! # Public-facing result: finite-dimensional approximants for even CARs
on two-link Borel argument & sup norm upgrading Y-limits (on boxes). -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey Vale VolumeCape
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(S:Finset Cover)(s:ℕ)
local notation "D₀" => aliasLaw Λ
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "K₀"=> (VolumeCape.Dream.plot l).K
local notation "T₀" => plaza (Λ:=Λ) S
local notation "L"=> Λ.R.L
local notation "nₛ" p:max=> side Y p s
local notation "n₁" p:max=> side Y p (s+1)

abbrev PairIdx (i k:ℕ):Prop:= (Y.voyage i).kick ≤ k ∧ s< Y.uv k
abbrev Page := Σ i:{j:ℕ×ℕ // PairIdx Y s j.1 j.2}, rawF (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S) × Common.Courses (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S) × Fields (side Y i.val.1 (s+1))
-- helpers inside Page namespace cannot use field notation because abbrev? define local notation.
namespace Page
variable (p: Page Y S s)
abbrev stage:= steps Λ.V (Y.ir p.1.1.1) Λ.block (Y.uv p.1.1.2) s
abbrev store:= ((Y.voyage p.1.1.1).X (Y.uv p.1.1.2)).gram (s+1)
abbrev rate:= ((Y.voyage p.1.1.1).X (Y.uv p.1.1.2)).wave s|>.val
end Page
variable (u:Chorus)
def edition (p: Page Y S s): Hall (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S)→ FC (Single (side Y p.1.1.1 (s+1))):= panelX T₀ C K₀ (nₛ p.1.1.1) (n₁ p.1.1.1) (apt (Y.ir p.1.1.1) Λ.block L s) (p.stage Y S s) Λ.K.j (p.rate Y S s) (p.store Y S s).J.M Λ.R.odd_side Chi.canonical Λ.J.d (p.store Y S s).beta u p.2.2.2 p.2.1 p.2.2.1

lemma algebra {h:Page Y S s} : 0<Λ.J.d ∧ 2*Λ.J.d < firstRadius SU.group:=by
 obtain ⟨x⟩:= (fullness Y h.1.1.1 h.1.1.2 h.1.2.1).cap_grant.grant s h.1.2.2
 exact x.legal
lemma die_env (p:Page Y S s):Envelope (edition Y S s u p):= xp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (legal Λ) ((algebra Y S s (h:=p)).1) ((algebra Y S s (h:=p)).2) -- .. placement wrong
lemma upholstery: Menu (edition Y S s u):=by
 let W:= Page Y S s; rcases isEmpty_or_nonempty W with e | e
 · refine ⟨Deal.congr (f:=fun (i:W)(x:Hall C T₀)=>edition Y S s u i x) ?_ (fun i=> isEmptyElim i),0,le_rfl,fun (i:W)=> isEmptyElim i⟩; exact fun ε _=>⟨∅,fun _ w=>False.elim (Finset.notMem_empty _ w), fun _ _ _ i=> isEmptyElim (i:W)⟩
 let n(p:W):=nₛ p.1.1.1; let t(p:W):=n₁ p.1.1.1
 have h(p:W):(t p).val=(n p).val*(L).val:=(apt (Y.ir p.1.1.1) Λ.block L s).exact_size
 have hx(p:W): (p.stage Y S s).kernel=(Course.dummy Λ).kernel:=by -- dummy uses K.bind, steps?
    exact (Y.pilot_steps s p.1.1.1 p.1.1.2).2.1
 have he(p:W): ‖(p.store Y S s).beta‖ ≤ Course.ceiling Λ s:=abs_le.mpr (Y.seated s p.1.1.1 p.1.1.2 p.1.2.2)
 refine matchbox C K₀ Λ.K.j Chi.canonical Λ.J.d ((algebra Y S s (h:=Classical.choice e)).1) ((algebra Y S s (h:=Classical.choice e)).2) u T₀ n t L h (Page.stage Y S s) (Page.rate Y S s) (fun p=> (p.store Y S s).J.M) Λ.R.odd_side (fun p=> (p.store Y S s).beta) (fun p=>p.2.2.2) (Course.dummy Λ) hx (fun p=>p.2.1) (fun p=> p.2.2.1) (legal Λ) he (Y':=Λ.R0 (hat Λ.R.L Λ.x s)) ?_
 intro p; exact ((Y.voyage p.1.1.1).X (Y.uv p.1.1.2)).pull.tip s p.1.2.2
variable (H:Real.exp 1 ≤ Λ.x)(v:Bracket S u)
-- knot_on private Library, recreate AtSupport once through language; make it nonprivate? build dependency time minimal via local copy
include H v
private lemma region_support (f:Purse S)(i:ℕ): AtSupport (Sound.treble u) (region S (nₛ i)) (knot (nₛ i) u f.val):=by
 have ht:= (note_t (tent Y H) u f.property v.tines).support (momentm Y i s); rw [kiosk] at ht
 exact fire (terrain Y H (Y.ir i) s) u S f.val ht
where
 fire{N M:Side}(e:N=M)(u S f)(h:AtSupport (Sound.treble u) (region S N) (knot N u f)):AtSupport (Sound.treble u) (region S M) (knot M u f):= by subst_vars; exact h
-- one fixed ε-net by representatives of the wide grammar itself; pays pair cutoffs satisfying *financed conditions* incl kick
local notation "Φ"=>sharp Y H s
local notation "χ"=> tent Y H
variable (i k:ℕ)
private lemma tip (x:Side): True:=trivial
private lemma typical : ∀ᶠ i:ℕ in atTop,Tipping T₀ (nₛ i) C:=by
 have ht:∀ᶠ m:Side in atTop, Tipping T₀ ((χ).c m) C:= separates (tent Y H) (tips (porch C T₀))
 filter_upwards [(momentum Y s).eventually ht] with i q; change Tipping _ (Λ.Ctor _ _) _; rw [←terrain Y H (Y.ir i) s]; exact q
local notation "C₁"=> liner (S.image (fun a=> Λ.R.L.val • a)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)
/- a local norm on coefficients in *each* marked CAR fixed word. All estimates pay on basisC & actual Campos. -/
def Tower (Λ:Preparation)(l:ℕ)(S:Finset Lattice.Cover):Set (Purse S):={g:Purse S| Satin.price Λ l S g.val ≤ 1}
lemma debt {x y:Purse S}(p:Page Y S s)(q:Tipping T₀ (nₛ p.1.1.1) C) (e:ℝ)(E:∀ (t:Page Y S s)(r:Courses C T₀), ‖∫ z:Hall C T₀, (amount C K₀ T₀ x.val r z - amount C K₀ T₀ y.val r z) • edition Y S s u t z∂law C T₀‖ ≤ e):
 let i:=p.1.1.1; let k:=p.1.1.2
 let X:=((Y.voyage i).X (Y.uv k)).gram
 ∀ W:Fields (side Y i (s+1)), ‖nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) X (Y.voyage i).CapeT Chi.canonical Λ.J.d (((Y.voyage i).X (Y.uv k)).wave) (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) s (knot (side Y i s) u (x.val-y.val)) W‖ ≤ e:=by
 intro i k U A; let w: Loom (side Y i s) := (Y.voyage i).CapeT s
 have z:Dream.Haven C K₀ (side Y i s) w:=((Y.voyage i).craft _)
 let h:=Sound.pastel x.property y.property
 refine cabaret S C K₀ (nₛ i) (n₁ i) (Vale.apt (Y.ir i) Λ.block L s) (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) Λ.K.j (p.rate Y S s) (U (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (U (s+1)).beta w (Journey.legal _) ((Y.voyage i).ownership s).paid.bill ((fullness Y i k p.1.2.1).cap_grant.branch s p.1.2.2) ((algebra Y S s (h:=p)).1) ((algebra Y S s (h:=p)).2) h u (region_support Y S s u H v ⟨_,h⟩ i) A z T₀ (liner_here S _) (linen_contains ..) q e (fun F r=> ?_)
 exact E ⟨p.1,F,r,A⟩ r
/-- Includes arbitrarily late k paying the stated gate for any such i,
with SAME choices of representatives, stronger than separate row approximants.
`m` (period-index floor) independent even of tolerance. -/
lemma patrons : ∃ m:ℕ, ∀ e:ℝ,0<e→∃ Z:Finset (Purse S),↑Z⊆Tower Λ l S ∧
    ∃ c:ℕ, ∀ f∈ Tower Λ l S,∃ t∈ Z, ∀ i ≥ m, ∀ k ≥ c, (Y.voyage i).kick≤ k → ‖Φ i k (note χ f.val u)-Φ i k (note χ t.val u)‖ < e:=by
 obtain ⟨m,n⟩:= eventually_atTop.mp (typical Y S s u H v); refine ⟨m,fun e p=>?_⟩
 obtain ⟨Y',p',z⟩:= library Y H C₁ (s+1); let ε:=e/(Y'+1); have he:0<ε:=by unfold ε; positivity
 have hl(x:Purse S)(r:Courses C T₀):Envelope (amount C K₀ T₀ x.val r):= amount_env C K₀ T₀ (Coeff.mono x.property (liner_here S _)) _
 obtain ⟨Z,B,m'⟩:= approximate_fleet (Common.law C T₀) (fun (x:Purse S) r=> amount C K₀ T₀ x.val r) hl (upholstery Y S s u) (die_env Y S s u) ε he
 obtain ⟨c,P⟩:= eventually_atTop.mp (z.and (Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+1)))
 refine ⟨Z,B,c,fun x p''=>?_⟩
 obtain ⟨y,A,h'⟩:=m' x p''; refine ⟨y,A,fun i t k pK G=>?_⟩
 have hx:Nonempty (Courses C T₀):=by
    obtain ⟨μ,hp,_,_⟩:= (Y.voyage i).craft s; exact Nonempty.map (chooseCourse C T₀ (side Y i s)) (nonempty_of_isProbabilityMeasure μ)
 let a:Page Y S s:= ⟨⟨(i,k),G,(P k pK).2⟩,1,(Classical.choice hx),1⟩ -- Nonempty Frame via arbitrary? have instance
 have hv:=debt Y S s u H v (x:=x) (y:=y) a (n i t) ε (fun j l=> le_of_lt (h' j l))
 obtain ⟨eq,hZ⟩:=exact_slope Y H S s u v i k x y G (P k pK).2
 rw [eq]
 refine ((P k pK).1 i G _ hZ ε hv).trans_lt ?_
 have ht':(Y'+1)*ε=e:=mul_div_cancel₀ _ (by linarith); linarith
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.patrons
