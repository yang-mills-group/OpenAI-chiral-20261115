import YM.SU5.FiniteGaugeData.Hills.ViewA
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace Hills
open Nacre Heat Charm Chrono Journey SalonG Terrace
variable (a j:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "T"=> StructureH Y h a W' R A
local notation "U"=> (StructureH Y h a W' R A).Unity
local notation "D"=> dip (U)
local notation "P'"=>planeP (U)
local notation "U'"=> cpo (U)
local notation "C"=> Camera Y h a W' R A
local notation "W1"=> W (tent Y h)
local notation "E'" f:max=> E s ((f:W (tent Y h)).val)
variable {x y:W (tent Y h)} (f:Plan Y h a d x)(A':A.space.Op)(e:0<d)
include A
variable (x) -- reorder redeclare? previously implicit x
omit A in
lemma house : ∃ (n:ℕ),0<n∧ ∃ z:ℤ,Plan Y h a n (clockW Kₜ a z x):= by obtain ⟨S,p⟩:=testimony Kₜ x; exact rent Y h S a x p

private abbrev tryPass := (house Y h a x).choose_spec
def steadyL (x:W (tent Y h)): (Camera Y h a W' R A).Op:=
 let S0:= tryPass Y h a x
 billC Y h s a _ W' R A S0.2.choose_spec S0.1
lemma steady_lease {z0:ℤ}(p:Plan Y h a d (clockW Kₜ a z0 x))(e:0<d): steadyL Y h s a W' R A x= billC Y h s a d W' R A p e:=by
 let T':=tryPass Y h a x; let f:= (house Y h a x).choose; let i:= (T'.2).choose; let t' :Plan Y h a f (clockW Kₜ a i x) := T'.2.choose_spec; unfold steadyL
 have hx: clockW Kₜ a (z0-i) (clockW Kₜ a i x)=clockW Kₜ a z0 x:=by rw [clock_add,sub_add_cancel]
 exact (repeat_int Y h s a f d W' R A t' T'.1 (z0-i) (Eq.mpr (congrArg (Plan Y h a d) hx) p) e).trans (bill_eq Y h s a d W' R A (Eq.mpr (congrArg (Plan Y h a d) hx) p) e p hx)
local notation "Ω" k:max=> steadyL Y h k a W' R A
lemma steady_price : steadyL Y h s a W' R A x=billC Y h s a d W' R A f e:=by
 let z:= tic_zero Kₜ a x; let h' :Plan Y h a d (clockW Kₜ a 0 x):= Eq.mpr (congrArg (Plan Y h a d) z) f; exact (steady_lease Y h s a d W' R A x (z0:=0) h' e).trans (bill_eq Y h s a d W' R A h' e f z)
lemma persist (z:ℤ): steadyL Y h s a W' R A (clockW Kₜ a z x)=steadyL Y h s a W' R A x:= by
 obtain ⟨d,e,i,p⟩:= house Y h a (clockW Kₜ a z x)
 have hx:= clock_add Kₜ a i z x; exact (steady_lease Y h s a d W' R A _ p e).trans ((bill_eq Y h s a d W' R A p e (Eq.mp (congrArg (Plan Y h a d) hx) p) hx).trans (steady_lease Y h s a d W' R A x (z0:=i+z) (Eq.mp (congrArg (Plan Y h a d) hx) p) e).symm)
lemma persist_space (z:ℤ): steadyL Y h s a W' R A (clockW Kₜ j z x)=steadyL Y h s a W' R A x:= by
 by_cases h':j=a; · subst j; exact persist ..
 obtain ⟨d,e,i,p⟩:= house Y h a x;
 have hx: clockW Kₜ a i (clockW Kₜ j z x)= clockW Kₜ j z (clockW Kₜ a i x):= clock_cross ..
 let v : Allows a j z:= fun p:j=a=> False.elim (h' p) -- typed function implicit goal `Allows`
 let t:=plan_walk Y h a j d (clockW Kₜ a i x) z h' p
 rw [← persist Y h s a W' R A _ i,hx, steady_price Y h s a d W' R A _ t e,←persist Y h s a W' R A x i, steady_price Y h s a d W' R A _ p e]; unfold billC; rw [← socialP Y h s a j W' R A _ z v,wicket_tangent ..,socialR]; exact h' -- check arg order steady_price `x` declared after f.
-- Linear maps. lease once enough.
variable {x}
lemma accountSum (x y:W (tent Y h)): steadyL Y h s a W' R A (x+y)=(Ω s) x+ (Ω s) y:=by
 obtain ⟨S,p⟩:= testimony Kₜ x; obtain ⟨S',u''⟩:= testimony Kₜ y
 obtain ⟨d,i,e,hx⟩:= rent_uniform Y h (S∪S') a
 let t:Plan Y h a d (clockW Kₜ a i x):= ⟨_,hx,loc_tic Kₜ _ a i (locate_sub Kₜ p subset_union_left)⟩; let u':Plan Y h a d (clockW Kₜ a i y):=⟨_,hx,loc_tic Kₜ _ a i (locate_sub Kₜ u'' subset_union_right)⟩
 rw [← persist Y h s a W' R A (x+y) i,clock_sum,←persist Y h s a W' R A x i,← persist Y h s a W' R A y i] -- oops rw changed occurrences x nested? rw ← persist ... only rewrites steadyL x
 rw [steady_price Y h s a d W' R A  _ (Plan.plus Y h t u') e,steady_price Y h s a d W' R A  _ t e,steady_price Y h s a d W' R A  _ u' e]; unfold billC; rw [wedge_sum Y h s a d W' R A t e u',social_sum]
lemma accountSub (x:W (tent Y h))(b:ℂ): steadyL Y h s a W' R A (b • x)= b • steadyL Y h s a W' R A x:= by
 obtain ⟨d,e,v,p⟩:=house Y h a x; rw [← persist Y h s a W' R A (b•x) v,←persist Y h s a W' R A x v,clock_scale]; rw [steady_price Y h s a d W' R A  _ (Plan.subsidy Y h p b) e,steady_price Y h s a d W' R A  _ p e]; unfold billC; rw [wedge_scale Y h s a d W' R A p e b, social_fee]
#print axioms persist_space
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
