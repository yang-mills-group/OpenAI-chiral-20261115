import YM.CF.Buffered.Suite
/-!
# Cloth rescaling inside native corner. Work on the untransformed period
 vectors with `patchQ` at N and `switchG` actual F. Any momentum sign charges
 paid already, no appeal to naturality on the rectangular gauge heaters at
 this level. Reconstruct the values on the two periodic fields. -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 19000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K V C F k v N P L D M B B' l c f: Side} {G:Gauge} {S:Patch}
-- elementary intertwining linear sums outside imaginary budget; enough through the actual column for all unmodified coarse modes.
section
variable {I J:Type*}[Fintype I][Fintype J][LinearOrder I][LinearOrder J](e:I↪ J) {A:Op I} {D:Op J}
local notation "c'" => coat e
lemma on_exp (h:∀ i, c' (acts A i)=acts D (c' i)) (x:Ket I): c' (acts (exp A) x)=acts (exp D) (c' x) := by
 have hp(k:ℕ)(x: Ket I): c' (acts (A^k) x)=acts (D^k) (c' x):=by induction k with|zero=> simp only [pow_zero,act_one]|succ k ih=> rw [pow_succ',pow_succ',act_mul,h,ih,act_mul]
 let V: Op I→ₗ[ℂ] Ket I:= ⟨⟨fun v=> acts v x,fun _ _=> act_add ..⟩,fun r a=> act_smul ..⟩
 let G: Op J→ₗ[ℂ] Ket J:= ⟨⟨fun v=> acts v (c' x),fun _ _=> act_add ..⟩,fun r a=> act_smul ..⟩
 let u:= LinearMap.toContinuousLinearMap ((coat e).comp V)
 have he:= (exp_series_hasSum_exp' (𝕂:=ℂ) A).mapL u -- tune
 have ht:= (exp_series_hasSum_exp' (𝕂:=ℂ) D).mapL (LinearMap.toContinuousLinearMap G)
 refine he.unique (a₂:= G (exp D)) ?_; convert ht using 1; funext k; rw [map_smul,map_smul]; exact congrArg (fun x=>_ • x) (hp k x)
 rfl
end
variable (A:Planck N P D)(Q:Op SU.Slot)
local notation "p'" => modeO A 0
local notation "t'" => pointO A 0
lemma slab_plank (x:Ket (Single P)): coat p' (acts (plankP P Q) x)=acts (plankP N Q) (coat p' x):=by
 nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul,basis_shell]; apply sum_congr rfl; intro i _; apply congrArg; apply PiLp.ext; intro v'
 by_cases p:v'∈lows p'
 · obtain ⟨l,t,rfl⟩:=Finset.mem_map.mp p; rw [←seamK,trails,basis_act,basis_act]; obtain ⟨⟨k,z⟩,i⟩:=i; obtain ⟨⟨u,w⟩,l⟩:=l; change jump (Equiv.refl _) (fun _=> (Aop-(1/2:ℂ) • 1) ⊗ₖ Q) (u,w,l) (k,z,i)=jump (Equiv.refl _) (fun _=> (Aop-(1/2:ℂ) • 1) ⊗ₖ Q) (t' u,w,l) (t' k,z,i); by_cases h:u=k
   · simp only [jump_apply]; rw [if_pos (show Equiv.refl _ u=k from h)]; rw [if_pos (show Equiv.refl _ (pointO A 0 u)=(pointO A 0 k) from congrArg t' h)] -- tune placeholder
   simp only [jump_apply,Equiv.refl_apply]; rw [if_neg h]; rw [if_neg (show ¬ t' u=t' k from fun a=> h ((t').injective a))] -- tune
 rw [basin _ _ _ p,basis_act]
 symm; obtain ⟨⟨v',s⟩,u⟩:=v'; obtain ⟨⟨i,t⟩,k⟩:=i
 change jump (Equiv.refl _) (fun _=> (Aop-(1/2:ℂ) • 1) ⊗ₖ Q) (v',s,u) (t' i,t,k)=_; rw [jump_apply, Equiv.refl_apply,if_neg ?_]
 intro u'; apply p; change v'=t' i at u'; subst v'; exact Finset.mem_map.mpr ⟨((i,s),u),mem_univ _,rfl⟩
lemma fee_equal (b:Bool)(x:Ket (Single P)): coat p' (acts (feeL b P Q) x)=acts (feeL b N Q) (coat p' x) :=by unfold feeL; split; exact on_exp _ (slab_plank A Q) x; exact on_exp _ (fun v=> by rw [act_neg,act_neg,map_neg,slab_plank]) x

section geom
lemma lime (x:Site P): natural (pointO A 0 x) = natural x:=by
 rw [dime]; funext i; unfold natural; change (↑(ZMod.val (((((x i).val:ℤ):Per N)))):ℤ)=_; rw [int_val _ (by positivity) (by have he:= Mail.width A; have hx:= (x i).val_lt; omega),Int.toNat_natCast]
-- no letter of marked coarse word sits near P seam. use interior margin.
variable {R w:ℕ}
include A
lemma wallpaper (K:Planck (More P) B k)(p:0<w)(x:Seat P)(h:x∈wallZ K 0 w): Damp (More P) w (natural x):=by
 obtain ⟨z,v,rfl⟩:=(Solid.seam ..).1 h
 have ht:= Mail.width K; rw [Planck.zone, show K.sail 0=0 from funext fun _=>by simp [Planck.sail],zero_add, Mail.oh (gauge_plan A) ?_]; all_goals intro i; specialize v i; omega
lemma salute (K:Planck (More P) B k)(x:Site P)(v:node x∈wallZ K 0 w)(h:2*R+1 ≤ w):∀ i:Axis, (R:ℤ)≤ natural x i ∧ natural x i+R<P.val := by
 let f:= node x; have hp: natural f=nodeC (natural x):=by
    rw [show f=wrap (More P) _ from (by rw [←node_of, Rush.nat_true] : f=wrap (More P) (nodeC (natural x)))]; apply Mail.oh (gauge_plan A); intro i; unfold nodeC natural; have he:= (x i).val_lt; rw [natM]; simp only [Pi.add_apply,two_smul,Pi.one_apply]; omega
 intro i; have he:= wallpaper A K (by omega) f v i; rw [hp,natM] at he; unfold nodeC at he; simp only [two_smul,Pi.add_apply,Pi.one_apply] at he; omega
lemma keeps_left (x z:Site P)(b:Cover)(h:x=z+wrap P b)(u:∀ i,(R:ℤ)≤ natural x i∧ natural x i+R<P.val)(p:size b≤ R) : natural z=natural x-b:=by
 rw [show z=wrap P (natural x-b) from by rw [map_sub,Rush.nat_true,h,add_sub_cancel_right]]; apply Mail.oh A; intro i; specialize u i; have he:(b i).natAbs ≤ R:=(Finset.single_le_sum (f:=fun i=> (b i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans p; rw [Pi.sub_apply]; omega
lemma boats (x z:Site P)(b:Cover)(u:∀ i,(R:ℤ)≤ natural x i∧ natural x i+R<P.val)(p:size b≤ R): (x=z+wrap P b) ↔ t' x=t' z+wrap N b :=by
 constructor; · intro e; rw [dime,dime, keeps_left A x z b e u p, ← map_add,sub_add_cancel]
 intro e; let L:= lesser₀ A
 apply Eq.trans ((stepR A 0 x).symm); rw [e,(slump A).port,stepR]
 -- tune
lemma tide (x:Site P)(b:Cover) : Rush.wind x b= Rush.wind (t' x) b ↔ Rush.wind x b= fee (periods N (natural x+b)) :=by unfold Rush.wind; rw [lime]
lemma erect_r (x z:Site P)(b:Cover)(h:x=z+wrap P b)(u:∀ i,(R:ℤ)≤natural x i∧ natural x i+R<P.val)(p:size b≤ R) : Rush.wind z b=Rush.wind (t' z) b:=by
 rw [tide]; rw [Rush.wind, keeps_left A x z b h u p, sub_add_cancel]; exact (Wings.toll_one x).trans (by rw [←lime A x]; exact (Wings.toll_one (t' x)).symm)
end geom
variable (A':Planck F f D)
variable {ℓ:F.val=N.val*S.L.val}{d:f.val=P.val*S.L.val}
local notation "r" => decreed ℓ
local notation "t" => decreed d
local notation "Y" => Iota (decreed ℓ)
local notation "T" => Iota (decreed d)
def nearX : Iota (decreed d) ↪ Iota (decreed ℓ) := Embedding.prodMap ((t').prodMap (Embedding.refl (St S.L))) (Embedding.refl SU.Slot)
local notation "f'" => modeO A' 0
local notation "J" => nearX (d:=d) (ℓ:=ℓ) A
lemma switches (i:T): switchG r (nearX A i)=f' (switchG t i):=by
 obtain ⟨⟨i,z,j⟩,q⟩:=i; change ((isle r (t' i,z),j),q) = ((pointO A' 0 (isle t (i,z)),j),q); rw [dime A', ←(show wrap F (natural (isle r (t' i,z)))= _ from Rush.nat_true _), data_isle _ S.odd_side, data_isle _ S.odd_side, lime]
lemma patch_here (u:Single P): J (patchQ t u)=patchQ r (p' u):=rfl
lemma headingZ (i:T): (slump (gauge_plan A')).cut (Peaks.touch r true (J i).1)= Peaks.touch t true i.1:=by
 change (slump (gauge_plan A')).cut (node (switchG r (J i)).1.1)=node (switchG t i).1.1; rw [switches A A']; change (slump (gauge_plan A')).cut (node (pointO A' 0 _))=_; rw [modes_step,stepR]; rfl
lemma caressed (i:T)(b:Bool): lobe r b (J i) (J i)=lobe t b i i:= (lobe_fine r b _ _).trans (lobe_fine t b _ _).symm

set_option quotPrecheck false
variable {R w:ℕ}(U:Pane f)(V:Pane P)(i l: Iota (decreed d))
local notation "e'" => weave (gauge_plan A') (show Config SU.group _ from U)
local notation "v'" => weave (gauge_plan A) (show Config SU.group _ from V)
local notation "E'" => Peaks.unionP (show Nom N F from (e',v'))
local notation "V'" => Peaks.unionP (show Nom P f from (U,V))
variable (j:ℕ)
local notation "τ" => tub (brix j S.L)
lemma one_tax (b:Cover)(u:size b ≤ R)(q p:St S.L)(o:Lattice.Order) (K:∀ i', (R:ℤ)≤natural l.1.1 i' ∧ natural l.1.1 i'+R<P.val):
 drag r true false q p b (τ b q p) o E' (J i) (J l)= drag t true false q p b (τ b q p) o V' i l:=by
 rw [drag_entry r j (show Nom N F from _) o q p,drag_entry t j (show Nom P f from _)]
 obtain ⟨⟨x,k⟩,a⟩:=i; obtain ⟨⟨y,g⟩,l⟩:=l
 change ite (k=q∧(t' y,g)=(t' x+wrap _ b,p)) _ 0=ite (k=q∧(y,g)=(x+wrap _ b,p)) _ 0; simp only [Prod.mk.injEq,(boats A y x b K u)]; split_ifs with h; swap; rfl
 rw [← show Rush.wind x b= Rush.wind (J ((x,k),a)).1.1 b from erect_r A y x b ((boats A y x b K u).2 h.2.1) K u]; change _ * _ * _ = _ * _ * _ -- tune
 have ht:= (slump (gauge_plan A')).traveller U (Peaks.touch r true (J ((x,q),a)).1) (runD true false (decreed d).count q p b o); rw [headingZ A A'] at ht; rw [show travel _ (Peaks.touch r true ((J ((x,k),a)).1.1,q)) _= _ from ht]; rfl
lemma scurf (K:Planck (More P) B k)(y:2*R+1≤w)(M: Male)(u:LaurentRadius j S.L R)(e:node l.1.1∈wallZ K 0 w):
 Peaks.cloth j M r E' (J i) (J l)=Peaks.cloth j M t V' i l:=by
 suffices he:mosaic r true false (tub (brix j (r).count)) E' (J i) (J l)=mosaic t true false τ V' i l by rw [cloth_entry,cloth_entry,he,caressed,caressed,caressed,caressed] -- tune
 rw [mosaic_entry r j u,mosaic_entry t j u]; apply congrArg; refine sum_congr rfl fun o _=> sum_congr rfl fun r' _=> sum_congr rfl fun p _=> sum_congr rfl fun v hv=> one_tax A A' U V i l j v ((Stencil.labels ..).1 hv) r' p o (salute A K _ e y)
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.fee_equal
#print axioms YM.CF.Buffered.Mail.scurf
