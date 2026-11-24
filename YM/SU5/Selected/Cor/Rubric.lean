import YM.SU5.Selected.Cor.Quiver
import YM.SU5.FiniteGaugeData.Pannier.Centrist
/-! # Structured mixed test. Uses `Mix` narrow true (first field) family, counts
homogeneous in *all 3* senses, allows products. Only within stated resolution/Parcel-like
prescription. No Haag claim. Center tag = number budget, dedicated PATCH chosen for whole tile.
Support sets in aperture's gauge units. Sector semantics = by constituent (NO free mark)
throughout every regulator (signed AP winding) and on limit FAMILY. No assuming
support-small outside representation. Keep homogeneous properties of two factors of final probes.
Using module algebra on *all* families despite commutation only on supported.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Lifted
open Window (family) -- maybe syntax invalid
open Py.Rate.Pannier
open Afterglow Afterglow.Tapestry
set_option synthInstance.maxSize 22000
attribute [local instance] opCStarAlgebra
namespace Rubric
-- native comparator; T location of Ward pulse; all creation necessarily outside. Row allows any later and earlier union. orientation remove north. today issue matter bands measured via gauge units for X.
variable (K:Calibration) (W: Window.Family)(D X Y:Finset Cover) -- patch, late-X, early-V
inductive Row (K:Calibration)(W:Window.Family)(D X Y:Finset Cover)(S:Finset Cover) : ℕ → ℕ→ℕ→Buffered.Family K→ Prop where
 | pull (u:Cover) (i:SpinIdx)(x:SU.Slot) : family x=W→ i∉ plusHalf→nodeC u∈S→nodeC u∈ X→ Row K W D X Y S 1 0 (if nodeC u∈ D then 1 else 0) (removal K u i x)
 | push (u:Cover)(i:SpinIdx)(x:SU.Slot) : family x=W→ i∈ plusHalf→ nodeC u∉ D→ nodeC u∈S→nodeC u∈ Y→Row K W D X Y S 0 1 0 (creation K u i x)
 | polo: Row K W D X Y S 0 0 0 1
 | zero {r m n}:Row K W D X Y S r m n 0
 | coeff {F r m n}(c:ℂ): Row K W D X Y S r m n F→ Row K W D X Y S r m n (c • F)
 | adds {F G r m n}:Row K W D X Y S r m n F→ Row K W D X Y S r m n G → Row K W D X Y S r m n (F+G)
 | grip {F G r m n a b c}: Row K W D X Y S r m n F→ Row K W D X Y S a b c G → Row K W D X Y S (r+a) (m+b) (n+c) (F * G)
abbrev cameo (r m:ℕ): Bool:= decide (Odd (r+m))
variable {K W D X Y}
namespace Row
variable {S T:Finset Cover}{r m n:ℕ}{F G:Buffered.Family K} (f:Row K W D X Y S r m n F)
local notation "Ω" => Row K W D X Y
include f
lemma wider (h:S ⊆ T):Ω T r m n F:=by
 induction f with
 | polo => exact .polo
 | zero => exact .zero
 | coeff c f p=> exact p.coeff c
 | adds _ _ h v=> exact h.adds v
 | grip _ _ h v=> exact h.grip v
 | push x i j a b c u v=> exact .push _ _ _ a b c (h u) v
 | pull x i j a b c u => exact .pull _ _ _ a b (h c) u
lemma assign : InTest K false S (cameo r m) F:= by
 induction f with
 | polo=> exact .one
 | zero=> exact .zero
 | push _ _ _ a b c d u=> exact .creator _ b d -- might b synt notation case
 | pull _ _ _ a b c d=> exact .remover _ b c
 | coeff a _ h=> exact .smul _ h
 | adds _ _ p q=> exact .add p q
 | @grip F G r m n a b c _ _ h q=> exact (show cameo (r+a) (m+b)= (cameo r m).xor (cameo a b) from (by unfold cameo; rw [add_add_add_comm r a m b]; by_cases x: Odd (r+m)<;> by_cases y: Odd (a+b) <;> simp [Nat.odd_add,x,y] <;> grind)) ▸ (InTest.mul h q : InTest _ _ _ _ _) -- orientation tune
-- SU.character. twistT orientation scalar ph^number. central outside. charge!
omit f
noncomputable def measCharge (W:Window.Family):= SU.z ^ (if W.2 then 2 else 4: ℕ)
noncomputable def flash (D:Finset Cover) (u:Cover): SU.E:= if u∈ D then SU.central else 1
lemma notStable(W:Window.Family)(k:ℕ)(v:¬ 5∣k): measCharge W^k≠1:= by
 unfold measCharge; rw [← pow_mul]; intro p; have hf:= SU.z_prim.dvd_of_pow_eq_one _ p; split at hf<;> omega -- Presburger
lemma lampZ (W:Window.Family): ‖measCharge W‖=1:= by unfold measCharge; rw [norm_pow,SU.z_n,one_pow]
private lemma chargedB (W:Window.Family)(a:SU.Slot)(h:family a=W): SU.charge a=if W.2 then 2 else 4:= by subst W; rcases a with ⟨a,b|b⟩ <;> rfl
private lemma flash_basis(u:Cover)(i:SpinIdx)(a:SU.Slot)(f:family a=W)(h:nodeC u∈ S){n:Side}(g:Seat n→SU.E)(q:TraceGauge S (flash D) g): acts (tradew n g).val (basisC n u i a)= (if nodeC u∈ D then measCharge W else 1) • basisC n u i a:=by
 rw [turn_basisC,q _ h]; unfold flash; by_cases p:nodeC u∈ D
 · rw [if_pos p,SU.by_charge,if_pos p,sum_eq_single a];
   · rw [Matrix.diagonal_apply_eq,measCharge, chargedB _ _ f]
   · intro y v t; rw [Matrix.diagonal_apply_ne _ t, zero_smul]
   simp
 simp [if_neg p, Matrix.one_apply]
include f
lemma paisley : Circular S (flash D) F ((measCharge W)^n • F):= by
 induction f with
 | polo=> rw [pow_zero,one_smul]; exact fun n u _ i=>(map_one _).symm
 | zero=> rw [smul_zero]; exact fun n u _ i=> (map_zero _).symm
 | push x i a h b c t v=>
    rw [pow_zero,one_smul]; intro m g k X'; change create _= twist _ (create (basisC (K.c m) x i a)); rw [twist_create,flash_basis _ _ _ h t g k, if_neg c,one_smul]
 | pull x i a h b c t=>
    intro m g k X'; change Fock.remove (basisC (K.c m) x i a)=twist (quantU (tradew _ g)) (measCharge W^(if nodeC x∈D then 1 else 0: ℕ) • Fock.remove (basisC (K.c m) x i a)); rw [twist_scalar,twist_remove,flash_basis _ _ _ h c g k]; by_cases z: nodeC x∈D
    · unfold Fock.remove; rw [if_pos z, if_pos z, pow_one, map_smul,star_smul,smul_smul,mul_comm,scale_unit_self (lampZ _),one_smul]
    rw [if_neg z, if_neg z, pow_zero,one_smul,one_smul]
 | coeff c _ h=> rw [smul_comm]; exact Circular.scale (flash D) S h c
 | adds _ _ p q=> rw [smul_add]; exact Circular.add (flash D) S p q
 | grip _ _ p q=> rw [pow_add,mul_smul,←Algebra.mul_smul_comm,←Algebra.smul_mul_assoc]; exact Circular.mul (flash D) S p q -- orientation `←`
end Row

variable (K W D X Y) (S:Finset Cover)(r m n:ℕ)
-- allow linear combinations over coefficient terms on SAME first pane. Structured vs abstract $Scopes` no opponents requiring purity.
def Marble : Submodule ℂ (Buffered.Family K):= Submodule.span ℂ {f| ∃ (g:PairsC → ℂ)(F:Buffered.Family K),Coeff false S g∧ Row K W D X Y S r m n F∧ f=scalar K g*F}
namespace Marble
variable {S} {T:Finset Cover}{K W D X Y} {r m n r' m' n':ℕ}{F G:Buffered.Family K}
variable (f:F∈Marble K W D X Y S r m n)
local notation "Ω" => Marble K W D X Y
lemma entry {a:PairsC→ℂ}(u:Coeff false S a)(z: Row K W D X Y S r m n F): scalar K a*F∈ Ω S r m n:= Submodule.subset_span (show _∈_ from ⟨a,F,u,z,rfl⟩)
lemma pure (g:Row K W D X Y S r m n F): F∈ Ω S r m n:=by
 have hf:=entry (Coeff.fromC false S (f:= 1) continuous_const (fun x y p=> rfl)) g
 rwa [show scalar K _=1 from funext fun m=>funext (fun x=>one_smul _ _),one_mul] at hf
include f
lemma assign: InTest K false S (cameo r m) F:=by
 refine Submodule.span_induction (p:=fun x _=> InTest _ _ _ _ x) (fun x h=>?_) (.zero) (fun _ _ _ _ p q=> .add p q) (fun a b _ v=> .smul a v) f
 obtain ⟨a,F,h,z,rfl⟩:=h; simpa using (InTest.mul (.seed h) z.assign) -- simpa may simp coeff false
lemma wider (h:S⊆ T) : F∈ Ω T r m n:= Submodule.span_mono (fun _ x=> by obtain ⟨a,F,v,u,e⟩:=x; exact ⟨a,F,v.mono h,u.wider h,e⟩) f
omit f
private lemma productB (a b: PairsC→ℂ)(h:Coeff false S a)(v:Coeff false S b) : Coeff false S (a*b):=by
 obtain ⟨f,hf,rfl⟩:=h.narrow rfl; obtain ⟨g,hg,rfl⟩:=v.narrow rfl
 refine ⟨fun _=> ⟨_,hf.mul hg,rfl⟩,Push.SectorMeasure.Env.compact ((hf.comp continuous_fst).mul (hg.comp continuous_fst)), fun x y p q=> congrArg₂ (· * ·) (h.locus x y p q) (v.locus x y p q)⟩
private lemma glueM {a b:PairsC→ℂ}(V W':Buffered.Family K): scalar K a*V*(scalar K b*W')= scalar K (a*b)*(V*W'):= by
 funext m P; let x:= (onC (K.c m) P.1,onC (K.c m) P.2); change ((a x • 1)*_)*((b x • 1)*_)= ((a x*b x) • 1)* (V m P * W' m P); rw [Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc (R:=ℂ),Algebra.smul_mul_assoc]; simp [Algebra.mul_smul_comm,smul_smul] -- tune `R`
include f
lemma grip (z:G∈ Ω S r' m' n'): F*G∈ Ω S (r+r') (m+m') (n+n'):= by
 let H:= Ω S (r+r') (m+m') (n+n')
 refine Submodule.span_induction (p:=fun x _=> x*G∈H) (fun x h=>?_) (by simp) (fun x y _ _ p q=> by rw [add_mul]; exact H.add_mem p q) (fun a x _ v=> by rw [Algebra.smul_mul_assoc]; exact H.smul_mem _ v) f
 obtain ⟨a,F,v,p,rfl⟩:=h; refine Submodule.span_induction (p:=fun y _=> (scalar K a*F)*y∈ H) (fun y x=>?_) (by simp) (fun x y _ _ p q=> by rw [mul_add]; exact H.add_mem p q) (fun t x _ v=> by rw [Algebra.mul_smul_comm]; exact H.smul_mem _ v) z
 obtain ⟨b,G,y,p',rfl⟩:= x; rw [glueM ..]; exact entry (productB _ _ v y) (p.grip p')
end Marble
-- modern comparator (Charge of structure not all). Stronger communicators matt∞ later)
local notation "Ω"=> Row K W D X Y S r m n
-- caller will bind r m n. use enough hypothesis directly. 
def Challenged (L:Buffered.Family K→ℂ): Prop:= ∀ (f:PairsC→ℂ)(x:Buffered.Family K), Coeff false S f→ Ω x→ L (scalar K f*x)= L (scalar K f)* L x
#print Challenged
open Row (measCharge flash)
variable {K W D X Y S r m n}{F G:Buffered.Family K}{L:Buffered.Family K→ℂ}
  (q:Scopes K S L)(t:cameo r m=false)(z:¬ 5∣ n)
include q t z
lemma unmixed (f: Ω F) : L F=0:=by
 by_contra v; have hp:InTest K true S false F:= t ▸ f.assign.widen; let w:=measCharge W^n; have hf:= q.gauge _ F (w • F) hp (.smul w hp) f.paisley; rw [q.scale F hp w] at hf; exact Row.notStable W n z (mul_right_cancel₀ v (hf.symm.trans (one_mul (L F)).symm))
lemma promises (f: F ∈ Marble K W D X Y S r m n)(k: Challenged K W D X Y S r m n L) : L F=0:=by
 let U:= Marble K W D X Y S r m n; have hc{x:Buffered.Family K}(h:x∈ U) : InTest K true S false x:= t ▸ (Marble.assign h).widen
 refine Submodule.span_induction (p:=fun x _=> L x=0) (fun x u=>?_) q.nil_v (fun _ _ h u p v=> by rw [q.plus_v _ _ (hc h) (hc u),p,v,add_zero]) (fun a x h p=> by rw [q.scale _ (hc h) a,p,smul_zero]) f
 obtain ⟨a,F,v,h,rfl⟩:=u; rw [k a F v h, unmixed q t z h,mul_zero]
end Rubric
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Rubric
#print axioms Row.assign
#print axioms promises
#print axioms Marble.grip
