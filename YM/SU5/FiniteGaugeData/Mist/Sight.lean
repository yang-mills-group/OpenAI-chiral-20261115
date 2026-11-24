import YM.SU5.FiniteGaugeData.Mist.Ladder
import YM.SU5.FiniteGaugeData.Mist.Lute
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
variable (S T₁: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
namespace Dover
variable (X:Engine Y h W' R a H)(q:Carousel Λ.R.L)(b:Axis)(B:List Axis)
variable (V:∀ a:Axis,Harbor Y h W' R Φ a)(T:∀ a:Axis,Engine Y h W' R a (V a))
open Leda Hike
open scoped NNReal ENNReal
variable {σ:Type}(s':σ→ℕ)(d':Axis→σ→ℕ)(p:∀ a x,0<d' a x)(x':σ→ W (tent Y h))(ν:Axis→ Prop)(v':∀ a,ν a→∀ x, Plan Y h a (d' a x) (x' x))(R₀:Axis→ List σ)(Z:List σ)
variable (x: σ→ Carousel Λ.R.L)(U:ν a)
abbrev carriesR (i:σ)(u:ν a):=social (Anteroom (T a).val) (HiPlay Y h W' R A S' a (V a) s' (d' a) (p a) x' (v' a u) i)
def laneVertex (v:Four ℝ):E4:= WithLp.toLp _ v
lemma lane_c : Continuous laneVertex:=by unfold laneVertex; fun_prop
-- crew
abbrev SteamV (x:Grid σ ℝ)(i j:σ):= coneT Y h W' R a H X ((x j a-x i a-office (Λ:=Λ) s' (d' a) i).toNNReal) * combT Y h W' R a H X (laneVertex (x j-x i)) Terrace.scheduleL
local notation "F"=> HiPlay Y h W' R A S' a (V a) s' (d' a) (p a) x' (v' a U)
local notation "Μ"=> TipH Y h W' R a H X
local notation "Q"=> casin Y h W' R A S' a H X
local notation "Y₁" a:max=> Dew Y h W' R a (V a) (T a)
local notation "Ω"=> (Y₁ a)
local notation "G"=> Lanes (Λ:=Λ) s' d' ν R₀
include S'
lemma transport(i j:σ) : social (Anteroom X.val) (signal Y h W' R a H X s' (d' a) x i j)= SteamV Y h W' R a H X s' d' (pixels L₁ x) i j:=by
 let v:=x j-x i; let t:=((↑((x j) a)-↑((x i) a)-office (Λ:=Λ) s' (d' a) i).toNNReal); have he:= Leda.comb_at X.val (Mist.liveL Λ) Terrace.scheduleL Terrace.scheduleL v (whimsy Y h W' R a H X) Terrace.scheduleV (fun i=>rfl)
 exact (Cot.citizen (B:=spireT X.val v) (home_base Y h W' R a H X Terrace.scheduleL t)).trans (congrArg (fun p:(TipH Y h W' R a H X).Op=>coneT Y h W' R a H X t * p) he)
lemma mRelay (i j:σ)(f:Grid σ ℝ→TipH Y h W' R a H X)(cf: Continuous f) : Continuous fun x:Grid σ ℝ=> SteamV Y h W' R a H X s' d' x i j (f x):= by
 let x(m:Grid σ ℝ):=laneVertex (m j-m i); let v(m:Grid σ ℝ):= (m j a-m i a-office (Λ:=Λ) s' (d' a) i).toNNReal; refine orchestra Terrace.scheduleL (whimsy Y h W' R a H X) Q (fun i=>unitC X.val Terrace.scheduleL (Mist.liveL Λ) (Terrace.scheduleV i)) x v (lane_c.comp ?_) (continuous_real_toNNReal.comp ?_) f cf
 · exact (continuous_apply j).sub (continuous_apply i)
 apply Continuous.sub _ continuous_const; fun_prop
include U
def picture (x:Grid σ ℝ):ℂ:= inner ℂ (Y₁ a) (TapeT (fun i=>carriesR Y h W' R A S' a V T s' d' p x' ν v' i U) (SteamV Y h W' R a (V a) (T a) s' d' x) Z (Y₁ a))
local notation "J₀" a:max z:max u:max => picture Y h W' R A S' a V T s' d' p x' ν v' z u
lemma picture_c : Continuous (picture Y h W' R A S' a V T s' d' p x' ν v' Z U):= (innerSL ℂ Ω).continuous.comp (payT (fun i=> carriesR Y h W' R A S' a V T s' d' p x' ν v' i U) _ (mRelay Y h W' R A S' a (V a) (T a) s' d') Ω Z)
lemma prospect (z:∀ a, ν a)(g: Accord a ν R₀)(b:(R₀ a).Nodup)(v:x∈ Lanes (Λ:=Λ) s' d' ν R₀): aspect Y h W' R A S' a (V a) (T a) s' (d' a) (p a) x' (v' a U) x (R₀ a)=picture Y h W' R A S' a V T s' d' p x' ν v' (R₀ a) U (pixels Λ.R.L x):=by
 classical
 let A':= Anteroom (T a).val; let L:= social A'; let X':= life_b -- tune clarify signatures
    Y h W' R A S' a V T s' d' p x' ν v' R₀ U Terrace.scheduleL g (fun b _=>z b) b x v
 refine X'.trans ?_; unfold picture; apply congrArg (inner ℂ Ω); exact DFunLike.congr_fun (same_tape _ _ _ _ (R₀ a) (fun _ _=>rfl) (fun i _ j _=> transport Y h W' R A S' a (V a) (T a) s' d' x i j)) Ω
lemma central (z:∀ a,ν a)(g:Accord a ν R₀)(j:(R₀ a).Nodup)(u:Grid σ ℝ)(v:u∈ WorksR (Λ:=Λ) s' d' ν R₀): picture Y h W' R A S' a V T s' d' p x' ν v' (R₀ a) U u= (J₀ b (R₀ b) (z b)) u:=by
 classical
 let f(a:Axis):= J₀ a (R₀ a) (z a); refine Leda.ensures (Mist.liveL Λ) _ (lanes_openR s' d' _ _) (f a) (f b) (picture_c ..) (picture_c ..) (fun v z' => ?_) v
 let g':=g.fits b (z b); have he:Accord b ν R₀:=⟨fun i v=> g'.symm.trans (g.fits i v)⟩; let x(a:Axis):=aspect Y h W' R A S' a (V a) (T a) s' (d' a) (p a) x' (v' a (z a)) v (R₀ a)
 have hA:x a=(f a) (pixels L₁ v):=prospect Y h W' R A S' a V T s' d' p x' ν v' R₀ v (z a) z g j z'; -- order? U before
 have hB:x b=(f b) (pixels L₁ v):=prospect Y h W' R A S' b V T s' d' p x' ν v' R₀ v (z b) z he (g'.nodup_iff.mp j) z'
 exact hA.symm.trans ((Dover.switch Y h W' R A S' a b V T s' d' p x' ν v' R₀ v (z a) g (z b) z').trans hB)
#print axioms central
end Dover
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
