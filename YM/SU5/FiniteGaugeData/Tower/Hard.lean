import YM.SU5.FiniteGaugeData.Tower.Palette
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
/-!
# Upper Borel input cards for the conditional kernel

Generic common patch/kernel across tori (identified for this Course in
`Course.pilot_steps`) with β allowed to vary in fixed observing-level interval.
Operator part paid separately. Even with the hard frame branches, a common
tolerance deck exists for *all perSite and perLink factors* of the kernel,
simultaneous on these variables; only applies to the link arguments being
used to read off the OUTPUT coefficients of the transfer -- they're grafted
from a fixed cover region, not claiming a hard-mask continuity result.
-/
open Push.GridApprox Tree Next.SectorChange Stencil Tap Tenant
section common
variable (S:Finset Cover)(P:Patch)(Z:KernelChoices)(p:P.Branches Z SU.group)
variable {X ι:Type*}[MeasurableSpace X](c f:ι→Side)(h:∀ i,(More (f i)).val=(More (c i)).val * P.L.val)
def fixedStep(i:ι):StepData (More (c i)) (More (f i)):=⟨P,Z,h i⟩
local notation "B"=> fixedStep P Z c f h
variable (V:X→LinksC)(hv: Measurable V)
local notation "Λ₁" i:max x:max=> Satin.graft S (f i) (V x)
local notation "D"=> Push.GridApprox.reach P
abbrev sliceP (P:Patch):=↥(Lattice.box (Push.GridApprox.reach P))
section mask
-- reduce patch b.f to one fixed cover lookup table
private def housing (Y:(sliceP P) × Axis→SU.E):LinksC := fun e=> if t:e.1∈ Lattice.box D then Y (⟨e.1,t⟩,e.2) else 1
private lemma inhabitedM:Measurable (housing P):=by
 apply measurable_pi_lambda; intro e; unfold housing; split; exact measurable_pi_apply _; exact measurable_const
include p hv
private lemma preFrame (i:(j:ι)→ Seat (c j))(t:ι→P.FrameTag):
 Palette (fun (j:ι)(x:X)=> P.frame Z (expandAt ((B j).ratio.embed (i j)) (Λ₁ j x)) (t j) : ι → X → P.Points→SU.E) ∧ Palette (fun j (x:X)=>P.frameMass Z (expandAt ((B j).ratio.embed (i j)) (Λ₁ j x)) (t j)):=by
 let R:=sliceP P × Axis
 let F(u:R)(j:ι)(x:X):SU.E:= expandAt ((B j).ratio.embed (i j)) (Λ₁ j x) (u.1.val,u.2)
 have hf(b:R):Palette (F b):=album_g S f V hv _
 have hz:= Palette.all hf
 have hP(j)(x:X): Agrees (Lattice.box D) (expandAt ((B j).ratio.embed (i j)) (Λ₁ j x)) (housing P (fun u:R=>F u j x)):=fun t u _=>by unfold housing; rw [dif_pos (show t.1∈Lattice.box D from u)]
 let a(j:ι)(x:X):=expandAt ((B j).ratio.embed (i j)) (Λ₁ j x)
 have tp(j x): P.frame Z (a j x) (t j)=P.frame Z (housing P (fun u:R=>F u j x)) (t j) ∧ P.frameMass Z (a j x) (t j)=P.frameMass Z (housing P (fun u:R=>F u j x)) (t j):=patch_dep P p _ (hP j x)
 change Palette (fun j (x:X)=> P.frame Z (a j x) (t j):ι→X→P.Points→SU.E) ∧ Palette (fun j (x:X)=>P.frameMass Z (a j x) (t j))
 simp_rw [(tp _ _).1,(tp _ _).2]; let m:= housing P
 constructor
 · refine Palette.instruction (σ:=P.FrameTag) (P:=P.Frame SU.group) (fun t j x=>P.frame Z (m (fun u:R=>F u j x)) t) (fun t=>hz.post _ ((P.frame_meas p t).comp (inhabitedM P))) t
 exact Palette.instruction (fun (t:P.FrameTag) j x=> P.frameMass Z (m (fun u:R=>F u j x)) t) (fun t=> hz.post _ ((P.frameMass_meas t).comp (inhabitedM P))) t

lemma mass_palette (i:(j:ι)→ Seat (c j))(t:ι→P.FrameTag):Palette (fun j (x:X)=> Push.GridApprox.perSite (B j) (Λ₁ j x) (i j) (t j)):= (preFrame S P Z p c f h V hv i t).2
lemma connector_palette (i:(j:ι)→ Edge (Seat (c j)))(t:(j:ι)→ Seat (c j)→ P.FrameTag): Palette (P:=P.Points→SU.E) (fun j (x:X)=> StepData.connector (B j) (G:=SU.group) (Λ₁ j x) (t j) (i j) : ι→ X→ P.Points→SU.E) := by
 let X₁(j:ι):= (i j).1+step (i j).2
 let A(r:(j:ι)→Seat (c j))(b:P.Points)(j:ι)(x:X):SU.E:= (B j).frames (Λ₁ j x) (t j) (r j) b
 have hp(r b):Palette (A r b):=((preFrame S P Z p c f h V hv r (fun a=> t a (r a))).1).post (fun i=> i b) (measurable_pi_apply _)
 let g(j:ι):= (B j).ratio.embed (i j).1
 let M (b:P.Points)(j:ι)(x:X):SU.E:= travel (expandAt (g j) (Λ₁ j x)) b.val (List.replicate P.L.val (posDir (i j).2))
 have hm(b:P.Points):Palette (M b):=by
    unfold M; simp_rw [travel_at]; exact palette_walk f (fun i x=>Λ₁ i x) (album_g S f V hv) P.L.val _ _ (by simp)
 have he(b:P.Points):Palette (fun j (x:X)=> StepData.connector (B j) (G:=SU.group) (Λ₁ j x) (t j) (i j) b : ι→X→SU.E):=
    ((hp _ b).both (hm b) (·*·) (continuous_fst.mul continuous_snd).measurable).both (hp X₁ b) (fun a b:SU.E=> a*b⁻¹) (continuous_fst.mul continuous_snd.inv).measurable
 exact Palette.all he

omit hv in
lemma site_bound (i:ι) (U:Config SU.group (More (f i)))(x:Seat (c i))(t:P.FrameTag):perSite (B i) U x t∈Set.Icc (0:ℝ) 1:=by -- i variable? introduce i:ι
 have hx(t:P.FrameTag): 0≤ perSite (B i) U x t:=by
    unfold perSite Patch.frameMass; split; positivity; split <;> positivity
 refine ⟨hx t,?_⟩; have hs : ∑ u:P.FrameTag,perSite (B i) U x u=1:= P.frameMass_sum p _
 exact ((single_le_sum (s:=univ) (f:=fun u=> perSite (B i) U x u) (fun i _=>hx i) (mem_univ t))).trans_eq hs
lemma site_deal (a:(j:ι)→Seat (c j))(t:ι→P.FrameTag): Menu (fun j (x:X)=>perSite (B j) (Λ₁ j x) (a j) (t j)):=by
 have hp:= mass_palette S P Z p c f h V hv a t
 exact ⟨hp.purchase isCompact_Icc (fun i x=>site_bound _ _ p _ _ _ _ _ _ _),1,zero_le_one,fun i x=> abs_le.mpr ((show _ ∧ _ from site_bound P Z p c f h i (Λ₁ i x) (a i) (t i)).imp_left fun a=> le_trans (by norm_num) a)⟩

end mask

variable {w:ℝ}(β:ι→ℝ)(v:∀i, |β i|≤w)
-- joint density factor, given prediction first
private lemma noise_continuous (i:ι): Continuous (fun x:ℝ×SU.E×SU.E=> noiseLink (B i) x.1 x.2.1 x.2.2):=by
 unfold noiseLink StepData.penaltyWeight
 exact (((Push.BetaTransport.penaltyZ_cont _ _).comp continuous_fst).inv₀ (fun x=> ((B i).penaltyZ_pos _).ne')).mul (by fun_prop)
private lemma shared(i j:ι)(a b:SU.E)(t:ℝ): noiseLink (B i) t a b=noiseLink (B j) t a b:=rfl
include p v hv
lemma link_cards (a:(j:ι)→Edge (Seat (c j)))(t:(j:ι)→ Seat (c j)→ P.FrameTag)(q:ι→SU.E): Menu (fun (j:ι)(x:X)=>perLink (B j) (β j) (Λ₁ j x) (t j) (a j) (q j)) := by
 rcases isEmpty_or_nonempty ι with I | v_; swap
 · let v':=Classical.choice v_; let W(j:ι)(x:X):P.Connector SU.group:= (B j).connector (Λ₁ j x) (t j) (a j)
   have he: Palette W:= connector_palette S P Z p c f h V hv a t
   let b(e:P.Points)(j:ι)(x:X):= P.predictorMass Z (W j x) e; let l(e:P.Points)(j:ι)(x:X):=P.predict Z (W j x) e
   have hx(e): Palette (b e):=he.post (fun r=> P.predictorMass Z r e) (P.predictorMass_meas e)
   have hW(e:P.Points)(j)(x:X):0≤ b e j x:=by unfold b Patch.predictorMass; split; positivity; exact P.weight_nonneg _
   have ht(e:P.Points)(j)(x:X): b e j x ≤ 1:=by
      have he : ∑ i:P.Points,b i j x =1:=P.predictorMass_sum ..; exact (single_le_sum (s:=univ) (f:=fun i=>b i j x) (fun i _=> hW i ..) (mem_univ _)).trans_eq he
   have hb(e:P.Points):Menu (b e):= ⟨(hx e).purchase (isCompact_Icc (a:=(0:ℝ)) (b:=(1:ℝ))) (fun i x=> ⟨hW e i x,ht ..⟩),1,zero_le_one,fun i x=> abs_le.mpr ⟨(by linarith [hW e i x]),ht ..⟩⟩
   have hl(e:P.Points):Deal (l e):=(he.post (fun r=>P.predict Z r e) (P.predict_meas p e)).clip_su
   have hp(e:P.Points):= (((Deal.pure (X:=X) (T:=fun _:ι=>ℝ) β).prod ((hl e).prod (Deal.pure (T:=fun _=>SU.E) q))))
   have hk(e:P.Points): Menu (fun j (x:X)=> noiseLink (B v') (β j) (l e j x) (q j)):= Menu.clip (Z:= (Set.Icc (-w) w) ×ˢ (Set.univ : Set (SU.E×SU.E))) (hp e) (isCompact_Icc.prod isCompact_univ) (fun j x=> ⟨abs_le.mp (v j),Set.mem_univ _⟩) (noise_continuous P Z c f h v')
   exact Menu.total (univ:Finset P.Points) (fun (e:P.Points)(j:ι)(x:X)=> b e j x * noiseLink (B v') (β j) (l e j x) (q j)) (fun j _=> (hb j).mul (hk j)) -- common rfl
 let DC:Menu (I:=ι) (X:=X) (T:=fun _=>ℝ) (fun i _=>0):= Menu.zero
 exact DC.congr (fun i=> isEmptyElim (i:ι))
end common
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.link_cards
