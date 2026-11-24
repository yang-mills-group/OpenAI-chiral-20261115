import YM.SU5.Reconstruction.Based.Profiles
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
open CF.Pannier.Chancel
variable {k:ℕ}(K:Calibration)(W:Window.Family)(p:Fin k→ Cover)
local notation "ρ" => removal K
local notation "π" => creation K
local notation "φ" => rootRemove R K
local notation "γ" => rootCreate R K
local notation "B" => Stitches K W p S
local notation "F" => Family K
local notation "D" l:max t:max => scene S K W p l t ρ π (scalar K)
local notation "Γ" l:max t:max => scene S K W p l t (rootRemove R K) (rootCreate R K) ((scalar K)∘ ask R)
variable {Q:Family K}{μ:Multiset Cover}{l:List (Fin k)}
section enroll
-- Change background via `H_x`. No change of profile/anchors. Keep narrow Coeff. DO NOT
-- equate F and Q yet (need singlet for that).
lemma takeSites (p₀:B ρ π l μ Q): ∃ Q':Family K, B (rootRemove R K) (rootCreate R K) l μ Q' ∧ ReadAs R K Q Q':=by
 induction p₀ with
 | empty=> exact ⟨_,.empty,ReadAs.one R K⟩
 | put i y c d a b s v u t g z h _ ih=> obtain ⟨Q',W',p'⟩:=ih; exact ⟨_,.put i y c d a b s v u t g z h W', ((ReadAs.removeLink R K z).mul (ReadAs.createLink R K g)).mul p'⟩
lemma takeScene(p₀:Q∈ D l μ): ∃ Q':Family K, Q' ∈ Γ l μ ∧ ReadAs R K Q Q':=by
 let L:= Γ l μ
 refine Submodule.span_induction (p:=fun x _=>∃ v∈ L,ReadAs R K x v) (fun f hp=>?_) ⟨0,L.zero_mem,ReadAs.zero R K⟩ (fun f g _ _ p q=> ?_) (fun i f _ x=>?_) p₀
 · obtain ⟨v,g,t,b,rfl⟩:=hp; obtain ⟨Q',A,B'⟩:= takeSites R K W p t; exact ⟨_,Submodule.subset_span (show scalar K (ask R g)*Q'∈ _ from ⟨Q',g,A,b,rfl⟩), (ReadAs.gaugeCoe R K b).mul B'⟩
 · obtain ⟨a,t,e⟩:=p; obtain ⟨b,v,c⟩:=q; exact ⟨a+b,L.add_mem t v,e.add c⟩
 obtain ⟨v,t,e⟩:=x; exact ⟨i • v,L.smul_mem _ t,e.scale i⟩
lemma takeComponent (p₀:Q∈raw S K W p μ) : ∃ Q':Family K,Q'∈ connected R K W p μ ∧ ReadAs R K Q Q':=by
 let L:= connected R K W p μ
 refine Submodule.span_induction (p:=fun x _=>∃ v∈ L,ReadAs R K x v) (fun f u=>?_) ⟨0,L.zero_mem,ReadAs.zero R K⟩ (fun f g _ _ p q=> ?_) (fun i f _ x=>?_) p₀
 · obtain ⟨l,t,v,h⟩:=u; obtain ⟨Q',A,B'⟩:=takeScene R K W p h; exact ⟨Q',Submodule.subset_span (show Q'∈ _ from ⟨l,t,v,A⟩), B'⟩
 · obtain ⟨a,t,e⟩:=p; obtain ⟨b,v,c⟩:=q; exact ⟨a+b,L.add_mem t v,e.add c⟩
 obtain ⟨v,t,e⟩:=x; exact ⟨i • v,L.smul_mem _ t,e.scale i⟩
lemma fromComponent (p₀:Q∈ raw S K W p μ)(h:Neutral K Q):Q∈ connected R K W p μ:=by
 obtain ⟨Q',A,q⟩:= takeComponent R K W p p₀; exact (expanding_neutral R K (FilTest (visible K W p μ S p₀)) (paid_on_charge R K W p A).visits h q).symm ▸ A
end enroll

section restore
-- conversely a connection program really is in that component. Including Profile.
lemma comp_narrow {a b:PairsC→ℂ}(p:Coeff false S a)(q:Coeff false S b) : Coeff false S (a*b) := by -- adapted Ablate
 obtain ⟨F',h,rfl⟩:= p.narrow rfl; obtain ⟨G,h',rfl⟩:= q.narrow rfl
 rw [show F'∘Prod.fst*(G∘Prod.fst)=(F'*G)∘(Prod.fst:PairsC→ LinksC) from rfl]; exact Coeff.fromC _ _ (h.mul h') fun x y v=> congrArg₂ (· * ·) (show F' x= F' y from p.locus (x,x) (y,y) v v) (show G x=G y from q.locus (x,x) (y,y) v v)
lemma mult_scalars(a b:PairsC→ℂ):scalar K (a*b)=scalar K a*scalar K b:=by
 funext m x; simp only [scalar,Pi.mul_apply,mul_smul,Algebra.smul_mul_assoc,one_mul]
lemma scalar_comm(A:F)(a:PairsC→ℂ): Commute A (scalar K a):=by
 ext m x:2; simp only [Pi.mul_apply, scalar,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,one_mul]
lemma off_leg_scale(x:Cover){a b:SU.Slot}(h:family a ≠ family b): scalar K (legColor R x a b)=0 ∧ scalar K (minusColor R x a b)=0:=by
 let hp(U:PairsC):legColor R x a b U=0:= congrFun (leg_family R x h) U.1
 constructor <;> (funext m v; simp [scalar,minusColor,hp])
lemma charge_renew {f:PairsC→ℂ}(p₁:Coeff false S f)(e:Q∈ D l μ): scalar K f * Q ∈ D l μ:=by
 refine Submodule.span_induction (p:=fun x _=> scalar K f*x ∈ D l μ) (fun g u=>?_) (by rw [mul_zero]; exact Submodule.zero_mem _)
   (fun _ _ _ _ p q=>by rw [mul_add]; exact Submodule.add_mem _ p q) (fun _ _ _ v=>by rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ v) e
 obtain ⟨w,g,k,v,rfl⟩:=u; rw [← mul_assoc,← mult_scalars]; exact Submodule.subset_span (show _∈ _ from ⟨w,_,k,comp_narrow p₁ v,rfl⟩)
lemma charge_word (p₀:B ρ π l μ Q): Q ∈ D l μ:= by
 have ht: Coeff false S 1:= Coeff.fromC false S (f:=1) continuous_const (fun _ _ _=>rfl)
 exact Submodule.subset_span (show Q∈ _ from ⟨Q,1,p₀,ht,by rw [Sound.unitLink,one_mul]⟩)

variable (i:Fin k)(y:Cover)(c d:SpinIdx)(a b:SU.Slot)(e:family a=W)(h:family b=W)(a₁:c∉plusHalf)(b₁:d∈plusHalf)(x:nodeC y∈ S)(z:nodeC (p i)∈ S)(u:∀ t,y≠p t)
include e h a₁ b₁ x z u
lemma charge_c (p₀:Q∈ D l μ): (removal K (p i) c a * creation K y d b)*Q∈ D (i::l) ((p i) ::ₘ y ::ₘ μ):=by
 let X:= removal K (p i) c a*creation K y d b; let O:= D (i::l) ((p i) ::ₘ y ::ₘ μ)
 refine Submodule.span_induction (p:=fun f _=> X*f∈ O) (fun g t=>?_) (by rw [mul_zero]; exact O.zero_mem)
   (fun _ _ _ _ h v=>by rw [mul_add]; exact O.add_mem h v) (fun _ _ _ v=> by rw [Algebra.mul_smul_comm]; exact O.smul_mem _ v) p₀
 obtain ⟨v,t,g,w,rfl⟩:=t; rw [(scalar_comm K X t).left_comm]; exact Submodule.subset_span (show _∈ _ from ⟨X*v,t,g.put i y c d a b e h a₁ b₁ x z u,w,rfl⟩) -- dot issue
lemma charge_up (p₀:Q∈ D l μ):(rootRemove R K (p i) c a * rootCreate R K y d b)*Q∈ D (i::l) ((p i) ::ₘ y ::ₘ μ):=by
 unfold rootRemove rootCreate; simp_rw [Finset.sum_mul,Finset.mul_sum,Finset.sum_mul]; refine Submodule.sum_mem _ fun m _=> Submodule.sum_mem _ fun n _=> ?_
 by_cases hm:family m=family a; swap; · rw [(off_leg_scale R K (p i) hm).2,zero_mul,zero_mul,zero_mul]; exact Submodule.zero_mem _
 by_cases hn:family n=family b; swap; · rw [(off_leg_scale R K y hn).1,zero_mul,mul_zero,zero_mul]; exact Submodule.zero_mem _
 let F₁:= minusColor R (p i) m a; let F₂:= legColor R y n b; let Q':= removal K (p i) c m; let P':= creation K y d n; change (scalar K F₁*Q')*(scalar K F₂ * P')*Q∈ _
 have hp (v:Family K) : scalar K F₁*Q'*(scalar K F₂*P')*v = scalar K F₁*(scalar K F₂*(Q'*P'*v)) := by simp_rw [mul_assoc]; rw [(scalar_comm K Q' F₂).left_comm]
 rw [hp]; exact charge_renew K W p (minus_narrow R false z m a) (charge_renew K W p (color_narrow R false x n b) (charge_c K W p i y c d m n (hm.trans e) (hn.trans h) a₁ b₁ x z u p₀))
omit e h a₁ b₁ x z u
lemma charge_view (p₀:B (rootRemove R K) (rootCreate R K) l μ Q): Q∈ D l μ:=by
 induction p₀ with
 | empty=> exact charge_word K W p .empty
 | put i y c d a b e h a₁ b₁ x z u H ih=> exact charge_up R K W p i y c d a b e h a₁ b₁ x z u ih
lemma restore_component (μ:Multiset Cover): connected R K W p μ ≤ raw S K W p μ:=by
 apply Submodule.span_le.mpr; rintro x ⟨l,h,t,v⟩; apply Submodule.subset_span; refine ⟨l,h,t,?_⟩
 suffices u: Γ l μ ≤ D l μ from u v; apply Submodule.span_le.mpr; rintro _ ⟨f,g,e,u,rfl⟩; exact charge_renew K W p (certified R u) (charge_view R K W p e)
end restore
end YM.CF.Buffered.Afterglow.Rooted
#print axioms YM.CF.Buffered.Afterglow.Rooted.restore_component
