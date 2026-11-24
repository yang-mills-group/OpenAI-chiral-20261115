import YM.SU5.Selected.Chene.Archer
import YM.Further.CURVED_GAUSSIAN_JETS.Horizon
import YM.Push.FREE_RESOLVENT.Flat
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Chene.Trunk
open Function Filter Matrix Lattice Tree SectorNext.Vacuum.FlatTree Finset Next.Rank.Axial Pad Precision Exterior RG FreeResolvent Further.CurvedGaussianJets
open scoped Topology BigOperators Matrix Kronecker
variable {c f : Side} (S:StepData c f) (F:Forest S.ratio)(T L:Bed)
local notation "p"=> S.kernel.penalty
local notation "P"=> YM.Precision.probe S
local notation "ξ"=> Flat.history S F T
local notation "I"=> Flat.rail S F
lemma railed : Flat.rail S F= (walk (Progress.StationaryScenes.Green.link F (S:=S)))ᵀ:=by ext i j; simp [Flat.rail,walk,Matrix.one_apply,eq_comm]
lemma sent : ((I).submatrix (wheel f) id) = (wrote F.trunks)ᵀ:=by
 rw [railed]; ext w v; let k:=Progress.StationaryScenes.Green.link F; change (1:Matrix _ _ ℝ) (wheel f v.val) (wheel f w)=(1:Matrix _ _ ℝ) v.val w; simp only [Matrix.one_apply,(wheel f).injective.eq_iff]
lemma operating : ξ= principal (rose p (pasture (T.metric.acts f)) (camp S)) F.trunks:=by
 let H:= T.metric.acts f; let d:= Exterior.d 1 f; let U:= wrote F.trunks; let V:=K H; let C:=camp S
 have he: ξ= Iᵀ*(V+p • (Pᵀ*P))*I:=by
    unfold Flat.history V K Fiber.principal Fiber.strength; simp only [transpose_mul, Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]; rfl
 rw [he,railed,transpose_transpose,pulse_min]; unfold V
 let k:=Progress.StationaryScenes.Green.link (S:=S) F
 have hX: rose p (pasture H) C=(K H+p • (Pᵀ * P)).submatrix (wheel f) (wheel f):=by
    unfold rose C pasture camp; rw [submatrix_add,submatrix_smul]; simp only [Pi.add_apply,Pi.smul_apply,transpose_submatrix, submatrix_mul_equiv]
 rw [show T.metric.acts f=H from rfl,hX]; rfl
lemma baseRoute : FreeResolvent.baseMatrix S T.metric= (rose p (pasture (T.metric.acts f)) (camp S)).submatrix (wheel f).symm (wheel f).symm:=by
 unfold rose pasture camp; rw [submatrix_add,submatrix_smul]; simp only [Pi.add_apply,Pi.smul_apply,transpose_submatrix,submatrix_mul_equiv,submatrix_submatrix]; simp [Function.comp_def, baseMatrix] <;> rfl -- tune
lemma colors(G:Gauge) : FreeResolvent.treeMatrix G S F T.metric= (ξ) ⊗ₖ (1: Matrix G.ColorIndex G.ColorIndex ℝ):=by
 rw [treeMatrix,fullMatrix,baseRoute S T,operating S F T]; ext ⟨i,a⟩ ⟨j,b⟩
 simp [FreeResolvent.tensor, Matrix.one_apply,plant, Pad.principal,ix, mul_ite] --
-- positivity kit
lemma pos_by_gap {J:Type*}[Fintype J][DecidableEq J]{A:Matrix J J ℝ}{a:ℝ}(s:Aᵀ=A)(ha:0<a)(h:Gap A a) : A.PosDef := by
 apply PosDef.of_dotProduct_mulVec_pos
 · ext i j; simpa only [IsHermitian,conjTranspose_apply,transpose_apply,star_trivial] using (Matrix.ext_iff.mpr s i j)
 intro x t; rw [star_trivial]; apply lt_of_lt_of_le ?_ (h.lower x)
 apply mul_pos ha; obtain ⟨i,hi⟩:= Function.ne_iff.mp t; exact (sq_pos_of_ne_zero (show x i≠0 from hi)).trans_le (le_normSum x i)
variable (Q:Towers S.patch.L)(G:Gauge)[Nonempty G.ColorIndex]
lemma green (a:ℝ)(ha:0<a)(l:Bid.Larger (G:=G) S)(g:Gap (T.metric.acts f) a)(s:(T.metric.acts f)ᵀ=T.metric.acts f) : (ξ).PosDef:=by
 let v:=treeFare G S.patch S.kernel a; let A:= FreeResolvent.treeMatrix G S F T.metric; have hA:Gap A v:= FreeResolvent.tree_gap S F T.metric l ha g
 let X:=ξ; let c:= Classical.arbitrary G.ColorIndex; let t(i:F.Free):= (i,c); have ht: X=A.submatrix t t:=by
    unfold A; rw [colors]; ext i j; simp [t,X]
 have hp0: Gap X v:= ht.symm ▸ (hA.submatrix t (fun i j he=> congrArg Prod.fst he))
 apply pos_by_gap _ (treeFare_pos _ _ _ ha) hp0
 change (ξ)ᵀ=ξ
 rw [operating,Pad.principal,transpose_submatrix]; simp only [rose,transpose_add,pasture_symm _ s]; rw [transpose_smul,transpose_mul,transpose_transpose]
lemma map_post (h:Towers.Diagonal S T L Q) (t:(ξ).PosDef) : p • 1- (((-p) • (camp S))*(wrote F.trunks)ᵀ)*(principal (rose p (pasture (T.metric.acts f)) (camp S)) F.trunks)⁻¹*(wrote F.trunks*((-p)•(camp S)ᵀ))=pasture (L.metric.acts c):=by
 let Γ:=K (L.metric.acts c); let M:= Flat.history S F T; let R:=camp S; let U:= wrote F.trunks; let V:=R*Uᵀ; let B:=P*I; let W:= p • Bᵀ
 have he:= (Flat.transfer S F T L Q h t).2
 change p • 1-Wᵀ*M⁻¹*W=Γ at he
 have hx:B.submatrix (wheel c) id=V:=by unfold V R B camp; rw [← sent S F]; exact (submatrix_mul_equiv ..).symm -- tune U
 rw [←operating]; change p • 1-_= Γ.submatrix _ _; rw [← he,submatrix_sub,submatrix_smul]; simp only [Pi.sub_apply,Pi.smul_apply,submatrix_one_equiv]; congr 1
 change (-p) • R*Uᵀ*M⁻¹*(U*((-p)• Rᵀ))=_
 let a:= wheel c
 have hh: (((B.submatrix a id) * M⁻¹)* (B.submatrix a id)ᵀ) = ((B*M⁻¹)*Bᵀ).submatrix a a:=by
    -- submatrix multiplication id
    let f:= Equiv.refl F.Free; calc
      _= ((B.submatrix a f)* (M⁻¹).submatrix f f)* Bᵀ.submatrix f a:= rfl
      _= _:= by rw [submatrix_mul_equiv,submatrix_mul_equiv]
 simp only [W, Matrix.mul_smul, Matrix.smul_mul,Matrix.transpose_smul,transpose_transpose,submatrix_smul,Pi.smul_apply]
 rw [← hh,hx,neg_smul,neg_smul,smul_neg,neg_neg,show U*Rᵀ=(R*Uᵀ)ᵀ from ?_]
 rw [transpose_mul,transpose_transpose]
#print axioms map_post
end YM.Chene.Trunk
namespace YM.Chene.Trunk
open Function Filter Matrix Lattice Tree SectorNext.Vacuum.FlatTree Finset Next.Rank.Axial Pad Precision Exterior RG FreeResolvent Further.CurvedGaussianJets
open scoped Topology BigOperators Matrix Kronecker
variable {c f : Side} (S:StepData c f) (F:Forest S.ratio)(T L:Bed)
def canopy (c:Side)(T:Bed) : Matrix (Reed c) (Reed c) ℝ:= pasture (T.metric.acts c)+(pin ℝ c)ᵀ*pin ℝ c
def Chene (c:Side)(T:Bed)(F:Finset (Reed c)):= (Pad.principal (canopy c T) F).det
lemma quantization (Q:Towers S.patch.L)(G:Gauge)[Nonempty G.ColorIndex](h:Towers.Diagonal S T L Q) (a:ℝ)(ha:0<a)(l:Bid.Larger (G:=G) S) (g:Gap (T.metric.acts f) a)(s:(T.metric.acts f)ᵀ=T.metric.acts f) (R:Finset (Reed f))(A:Finset (Reed c))(r: Arbor (sky f) R)(v:Arbor (sky c) A) : S.kernel.penalty^(Fintype.card (Reed c))* Chene f T R=(Flat.history S F T).det* Chene c L A :=by
 let D:=T.metric.acts f; let X:=Flat.history S F T; have hp:X.PosDef:=green S F T G a ha l g s; obtain ⟨p,p'⟩:= rebates S; rw [operating]; exact Pad.plateau _ _ _ _ _ _ _ R F.trunks A (arbor_current S.ratio R r) (buildup S.ratio F A v) (pasture_symm _ s) S.kernel.penalty_pos.ne' (loft ..) p p' _ (pasture_r D) (pin_wind f) (moves S) (by rw [← operating]; exact IsUnit.mk0 _ hp.det_pos.ne') (map_post S F T L Q h hp)
end YM.Chene.Trunk
#print axioms YM.Chene.Trunk.quantization
#print axioms YM.Chene.Trunk.colors
