import YM.CF.Vp929.Contour.Halo
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Larch Push.AbsoluteSums Trees Wray Nor
variable {a b h₀:ℝ}{A A':Pax n}{B B':Cusp n}
lemma nextHue {X Y:Support (More n)}{F:Copy n}(q:Vow.Medal P X Y F h a)(z:ℂ): Vow.Medal P X Y (z • F) h (‖z‖*a):=by
 obtain ⟨Z,b,u,w,v'⟩:=q; refine ⟨⟨fun i j f g=> congrArg (z • ·) (Z.same i j f g),fun i=>(Z.lit i).smul z,Z.keeps.const_smul z,fun i j=>?_⟩,‖z‖ • b,fun i=>mul_nonneg (norm_nonneg _) (u i),fun i s _ t=>?_ ,?_ ⟩
 · let X:= hueV (tradew _ j); change z • _= X (z • _); rw [Z.gaugeX,map_smul]; rfl
 · let p:=w i s t; refine ⟨Eventually.of_forall (fun y=> (fineShape _).allP),fun j=>?_⟩; exact (p.haveP j).σ z
 unfold joinV; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖,← mul_sum]; exact mul_le_mul_of_nonneg_left v' (norm_nonneg _)
private lemma shade (A:Aura n→ℝ)(z:ℝ)(o:Seat n): tallB (z • A) P.B h₀ o=z*tallB A P.B h₀ o:=by unfold tallB; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,mul_sum]
namespace MonoQ
protected lemma add (p:MonoQ P h h₀ A a)(q:MonoQ P h h₀ A' b): MonoQ P h h₀ (A+A') (a+b):=by obtain ⟨r,P₀,f⟩:=p; obtain ⟨s,Q₁,g⟩:=q; refine ⟨r+s,fun i=>(P₀ i).plus (Q₁ i),fun i=>?_⟩; rw [tall_add]; exact add_le_add (f i) (g i)
protected lemma scale (p:MonoQ P h h₀ A a)(z:ℂ): MonoQ P h h₀ (z • A) (‖z‖*a):=by obtain ⟨r,Q₁,f⟩:=p; refine ⟨‖z‖ • r,fun i=>nextHue (Q₁ i) z,fun i=>?_⟩; rw [shade (P:=P)]; exact mul_le_mul_of_nonneg_left (f i) (norm_nonneg _)
protected lemma sub (p:MonoQ P h h₀ A a)(q:MonoQ P h h₀ A' b): MonoQ P h h₀ (A-A') (a+b) := by simpa [sub_eq_add_neg] using p.add (q.scale (-1))
protected lemma purse (p:MonoQ P h h₀ A a)(q:a ≤ b):MonoQ P h h₀ A b:= by obtain ⟨r,g,u⟩:= p; exact ⟨r,g,fun i=> (u i).trans q⟩
protected lemma fade (p:MonoQ P h h₀ A a)(q:b ≤ h₀)(v:0≤h) : MonoQ P h b A a:= by obtain ⟨r,g,u⟩:=p; exact ⟨r,g,fun z=>(tall_m _ (fun i=> (g i).wage v) q z).trans (u z)⟩
protected lemma zero : MonoQ (n:=n) P h h₀ 0 0:= ⟨0,fun i=> Vow.Medal.zeroT, fun i=> by simp [tallB]⟩
end MonoQ
namespace Packed
protected lemma add (p:Packed P h h₀ B a)(q:Packed P h h₀ B' b): Packed P h h₀ (B+B') (a+b):=by obtain ⟨r,P₀,f⟩:=p; obtain ⟨s,Q₁,g⟩:=q; refine ⟨r+s,⟨add_nonneg P₀.1 Q₁.1,fun i D u v=>(P₀.2 i D u v).plus (Q₁.2 i D u v)⟩,fun i=>?_⟩; rw [tall_add]; exact add_le_add (f i) (g i)
protected lemma scale (p:Packed P h h₀ B a)(z:ℂ): Packed P h h₀ (z • B) (‖z‖*a):=by obtain ⟨r,Q₁,f⟩:=p; refine ⟨‖z‖ • r,⟨fun i=> mul_nonneg (norm_nonneg _) (Q₁.1 i),fun i D u v=>nextHue (Q₁.2 i D u v) z⟩,fun i=>?_⟩; rw [shade (P:=P)]; exact mul_le_mul_of_nonneg_left (f i) (norm_nonneg _)
protected lemma sub (p:Packed P h h₀ B a)(q:Packed P h h₀ B' b): Packed P h h₀ (B-B') (a+b) := by simpa [sub_eq_add_neg] using p.add (q.scale (-1))
protected lemma purse (p:Packed P h h₀ B a)(q:a ≤ b):Packed P h h₀ B b:= by obtain ⟨r,g,u⟩:= p; exact ⟨r,g,fun i=> (u i).trans q⟩
protected lemma fade (p:Packed P h h₀ B a)(q:b ≤ h₀)(v:0≤h) : Packed P h b B a:= by obtain ⟨r,g,u⟩:=p; exact ⟨r,g,fun z=>(tall_m _ g.1 q z).trans (u z)⟩
protected lemma zero : Packed (n:=n) P h h₀ 0 0:= ⟨0,⟨le_refl _,fun i=> fun D u v=> Vow.Medal.zeroT⟩, fun i=> by simp [tallB]⟩
end Packed
namespace Marked
protected lemma add (p:Marked P h h₀ B a)(q:Marked P h h₀ B' b): Marked P h h₀ (B+B') (a+b):=by obtain ⟨r,P₀,f⟩:=p; obtain ⟨s,Q₁,g⟩:=q; refine ⟨r+s,fun i D u=>(P₀ i D u).plus (Q₁ i D u),fun i=>?_⟩; rw [show Vow.hymn (r+s)=Vow.hymn r+Vow.hymn s from (funext fun z=>by change ∑ i∈fullD z,(r z i+s z i)=_; rw [sum_add_distrib]; rfl),tall_add]; exact add_le_add (f i) (g i)
protected lemma scale (p:Marked P h h₀ B a)(z:ℂ): Marked P h h₀ (z • B) (‖z‖*a):=by obtain ⟨r,Q₁,f⟩:=p; refine ⟨‖z‖ • r,fun i D u=>nextHue (Q₁ i D u) z,fun i=>?_⟩; rw [show Vow.hymn (‖z‖ • r)= ‖z‖ • Vow.hymn r from (funext fun t=>by change ∑ i∈fullD t,(‖z‖ * r t i)= ‖z‖ * ∑ i∈fullD t,r t i; rw [mul_sum]),shade (P:=P)]; exact mul_le_mul_of_nonneg_left (f i) (norm_nonneg _)
protected lemma sub (p:Marked P h h₀ B a)(q:Marked P h h₀ B' b): Marked P h h₀ (B-B') (a+b) := by simpa [sub_eq_add_neg] using p.add (q.scale (-1))
protected lemma purse (p:Marked P h h₀ B a)(q:a ≤ b):Marked P h h₀ B b:= by obtain ⟨r,g,u⟩:= p; exact ⟨r,g,fun i=> (u i).trans q⟩
protected lemma fade (p:Marked P h h₀ B a)(q:b ≤ h₀)(v:0≤h) : Marked P h b B a:= by obtain ⟨r,g,u⟩:=p; exact ⟨r,g,fun z=>(tall_m _ (fun i=> sum_nonneg fun j p=>(g i j p).wage v) q z).trans (u z)⟩
protected lemma zero : Marked (n:=n) P h h₀ 0 0:= ⟨0,fun i=> fun D u=> Vow.Medal.zeroT, fun i=> by simp [tallB,Vow.hymn]⟩
end Marked
end YM.CF.Py.Rate
