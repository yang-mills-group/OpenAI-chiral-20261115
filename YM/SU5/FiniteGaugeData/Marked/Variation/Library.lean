import YM.SU5.FiniteGaugeData.Marked.Variation.Bankroll
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake

/-! # Estimate in the election application. Keep costs for arbitrarily
many CAR letters (fixed in taking the limits); shared canonical chiral system.
Use Sharp steps here, don't need Uniform even RP at next level again but its
consequence `Homes` on the Sharp ratios.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)(s:ℕ)
omit h in
private lemma castHomes {n m:Side}(p:m=n)(v:Loom n)(t:Mark n→ℂ)(D:ℝ)
    (q:∀ g:Mark m, AtSupport false (region S m) g → ‖t (p ▸ g)‖ ≤ D*cash (p.symm ▸ v) g) :
    ∀ g:Mark n,AtSupport false (region S n) g → ‖t g‖ ≤ D*cash v g:=by subst m; exact q
include h
lemma library:∃ D:ℝ,0<D ∧ ∀ᶠ k:ℕ in atTop, ∀ i:ℕ,(Y.voyage i).kick ≤ k→
 let n:= side Y i s
 ∀ g:Mark n, AtSupport false (region S n) g → ∀ y:ℝ, (∀ x,‖g x‖ ≤ y) → ‖Journey.compass Y i k s g‖ ≤ D*y:=by
 obtain ⟨D,d,t⟩:= Homes Y h s S; refine ⟨D,d,t.mono fun k p i q=> ?_⟩
 let n:= side Y i s; let v:= (Y.voyage i).CapeT s; let A:=Journey.compass Y i k s
 have he:= castHomes S (terrain Y h (Y.ir i) s) v A D (p i q)
 intro _ g h y e; refine (he g h).trans (mul_le_mul_of_nonneg_left ?_ d.le)
 unfold cash; have ht:= h.env; apply (integral_mono (cashable ((Y.voyage i).ownership s).paid.bill ht) (integrable_const (μ:=city _) y) (fun _=>e _)).trans_eq; simp
private theorem knot_on {f}(u:Chorus)(v:Bracket S u)(q:Coeff true S f)(i:ℕ):
 let g:=knot (side Y i s) u f
 send Y h i s (note (tent Y h) f u (momentm Y i s))=g ∧ AtSupport false (region S (side Y i s)) g:=by
 have hz(m:Side):= (v.harmony ▸ (note_t (tent Y h) u q v.tines).support m:AtSupport false _ _); simp_rw [kiosk] at hz
 rw [kiosk]
 exact castD S u f _ _ (terrain Y h (Y.ir i) s) (hz _)
where
 castD(S: Finset Cover)(u f)(n m:Side)(h:n=m)(p:AtSupport false (region S n) (knot n u f)):(show Mark m from h ▸ knot n u f) = knot m u f ∧ AtSupport false (region S m) (knot m u f):= by subst n; exact ⟨rfl,p⟩

local notation "D₀" => aliasLaw Λ
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "D"=> (VolumeCape.Dream.plot l).K

def plaza := liner S (Advance.nearZero (aliasLaw Λ))
local notation "T" => plaza (Λ:=Λ) S -- does plaza parameter Λ implicit?
def price (Λ:Preparation)(l:ℕ)(S:Finset Cover)(f:PairsC→ℂ) := Touch (plaza (Λ:=Λ) S) l f

variable (u:Chorus)(v:Bracket S u)
-- mark-subtract in the physical system and bound directly by above library
local notation "B₀"=> Λ.block
local notation "L"=> Λ.R.L
open Vale
local notation "T'"=> liner (S.image (fun a=> Λ.R.L.val • a)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J) -- gross dotted?
local notation "X" i:max k:max => ((Y.voyage i).X (Y.uv k)).gram
local notation "R" i:max=> (Y.voyage i).CapeT
local notation "Q" i:max k:max=> ((Y.voyage i).X (Y.uv k)).wave
local notation "θ" i:max k:max z:max=> nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) (X i k) (R i) Chi.canonical Λ.J.d (Q i k) (steps Λ.V (Y.ir i) B₀ (Y.uv k)) s (knot (side Y i s) u z)
variable (i k:ℕ)
include v
set_option maxHeartbeats 350000 in
lemma exact_slope(f g:Purse S)(t:(Y.voyage i).kick≤ k)(p:s< Y.uv k):
 sharp Y h s i k (note (tent Y h) f.val u)-sharp Y h s i k (note (tent Y h) g.val u)=Journey.compass Y i k (s+1) (θ i k (f.val-g.val)) ∧ AtSupport false (region (T') (side Y i (s+1))) (θ i k (f.val-g.val)):=by
 have hl:= fullness Y i k t; let a:= hl.cap_grant; let A:= steps Λ.V (Y.ir i) B₀ (Y.uv k); let x:=f.val-g.val; let n:= side Y i s; let F(q:PairsC→ℂ):= knot n u q
 obtain ⟨U⟩:= a.grant s p; have hf:=knot_on Y h S s u v f.property i; have hg:=knot_on Y h S s u v g.property i; have hz:=knot_on Y h S s u v (Sound.pastel f.property g.property) i
 have he: F f.val - F g.val=F x:= by ext1 v; unfold F knot; simp [x, sub_smul]
 let Z:= X i k
 let U':= (R i) s; let X':= Z s
 have mu: Measurable U':=((Y.voyage i).ownership s).paid.bill
 have Hν:= mark_integrable mu hf.2.env (Marks.can_read _ _ X' U' (Y.each_level i k s t p.le))
 have hν:= mark_integrable mu hg.2.env (Marks.can_read _ _ X' U' (Y.each_level i k s t p.le))
 have ht:markedRead (F x) U' (denZ X' Λ.U U')= markedRead (F f.val) U' (denZ X' Λ.U U')- markedRead (F g.val) U' (denZ X' Λ.U U'):=by
    rw [←he, sub_eq_add_neg, ←neg_one_smul ℂ (F _),mark_add mu hf.2.env ((hg.2.smulM (-1)).env) (Marks.can_read _ _ X' U' (Y.each_level i k s t p.le)), mark_smul, neg_one_mul]; abel
 have hX:= single_num Λ.U Z (Y.voyage i).CapeT Chi.canonical Λ.J.d (Y.uv k) ((Y.voyage i).X (Y.uv k)).wave A (legal Λ) a (hz.2.mono (Finset.subset_univ _)) p -- legal ambiguous
 constructor
 · change Journey.compass Y i k s (send Y h i s _) - Journey.compass Y i k s (send Y h i s _)=_
   rw [hf.1,hg.1]; unfold Journey.compass; rw [←sub_div,←ht,hX,((Y.voyage i).X (Y.uv k)).balance s p.le,← ((Y.voyage i).X (Y.uv k)).balance (s+1) p]
 obtain ⟨y,b,c,F0,s'⟩:= U.cap
 have H:= surround (Vale.apt (Y.ir i) Λ.block L s) (A s) Λ.K.j ((Q i k) s).val (Z (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Z (s+1)).beta U' (show LaurentRadius Λ.K.j L D₀ from legal Λ) F0.bill (a.branch s p) U.legal.1 U.legal.2 _ hz.2 (tissue Y i s) (a.aligned s p)
 have eq:(A s).patch.J=Λ.R.J:=a.radius s p; rw [eq] at H
 exact H.mono (next_contains S _ n (apt ..))
