import YM.SatinExist.Purchaser
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Set
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
local notation "H"=> P.ColorHil 3 (β)
local notation "B"=> P.par.block
local notation "l₀"=> P.width
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ρₛ" t:max=> Selected.gaugeMesh Λ t
local notation "θ" t:max => Selected.gaugePosition Λ t
local notation "ℓ"=> P.calibration.ℓ
-- matter mode aperture. NO links in these initial-height operands; do not propagate gauge independence to finer tests; authorize CP18.
def atOne (q:Cover)(i:Fin 2) : Twah:= ⟨q,q,i,i,[],rfl⟩
noncomputable def equinox (q:Cover)(R:ℕ) : P.Test:= P.tuneK (Gemini.flourish (R:=R) (atOne q 0) Z)
variable (q:Cover)(R:ℕ)
local notation "X"=> P.equinox Z q R
open Sods
lemma currentCAR (m:Side)(f:Fields (P.calibration.c m)) : (P.equinox Z q R).val m f = Twah.gold R •
    ∑ i∈Window.colors Z,(Fock.remove (basisC ((K).c m) q (dnSpin 0) i))* (Fock.create (basisC ((K).c m) q (upSpin 0) i)) :=by
 let A:=atOne q 0; let L:= Window.colors Z; let n:= P.calibration.c m
 let Uv(i j:SU.Slot):= Fock.remove (basisC n q (dnSpin 0) j)*Fock.create (basisC n q (upSpin 0) i)
 change (A.groundWord R Z) n f= Twah.gold R • _
 unfold Twah.groundWord; apply congrArg; refine Finset.sum_congr rfl fun i h=> ?_
 change ∑ j∈L,A.coil f.1 i j • Uv i j=Uv i i
 have hv(j):A.coil f.1 i j=(1:Op SU.Slot) i j:=by unfold Twah.coil; rw [show A.laps f.1=1 from rfl,map_one]; rfl
 rw [Finset.sum_eq_single_of_mem i h, hv,Matrix.one_apply_eq,one_smul]; intro j _ t; rw [hv,Matrix.one_apply_ne t.symm,zero_smul]
lemma pieces_blue : PureMatter K (P.equinox Z q R) ∧ P.equinox Z q R∈enclave K ∧ P.equinox Z q R ∈ bay K ({nodeC q}: Finset Cover) false:= by
 let q':= Gemini.flourish (atOne q 0) Z (R:=R); refine ⟨fun i z q=> Eq.trans (P.currentCAR Z _ R i z) (P.currentCAR Z _ R i q).symm,P.celebrity q',?_⟩
 let f:InTest K false (atOne q 0).patio false (X).val:=q'.1.narrow P.calibration
 rw [show (atOne q 0).patio={nodeC q} from ?_] at f; exact (Tapestry.locates ..).2 f
 unfold atOne Twah.patio; simp [visits]
noncomputable def centeredSun (U:P.Test) : P.Test:= U - P.singleState 3 s x U • 1
local notation "μ" => P.singleState 3 s x
@[simp] lemma centeredSun_good (U:P.Test): μ (P.centeredSun x s U)=0:= by
 unfold centeredSun; rw [map_sub,map_smul,P.single_state _ _ x 1,P.reading_unit,map_one,smul_eq_mul,mul_one,sub_self]
lemma cent_sun (U Vp:P.Test) : μ (P.centeredSun x s U*P.centeredSun x s Vp) = μ (U*Vp)-μ U*μ Vp := by
 have hA(v:ℂ)(w:P.Test): μ (v • w)=v* μ w:= map_smul (μ) v w
 rw [centeredSun,mul_comm,_root_.mul_sub,map_sub, mul_comm, centeredSun, _root_.mul_sub,map_sub, mul_smul_comm,mul_one,hA, mul_smul_comm, mul_one] -- tune
 simp only [show μ (Vp - μ Vp • 1) = 0 from centeredSun_good ..,hA,zero_mul,sub_zero,mul_comm (μ U)]
-- UV direct tangible fidelity
local notation "η" i:max=> P.singleState 3 (c i) x
local notation "Ft" v:max i:max=> discrete (r (i:ℕ)) v
variable {P r x c} (A:Launch P c r){d:ℕ→ℝ}(h:readyUV P c r x d)(u:Tendsto d atTop (𝓝 0))
include A h u
-- any plane p. allow same point on both ends *inside one marker* i.
lemma one_bra {w:ℕ}(Q:Fin w → Gaia)(Z:Fin w→Lead.Clan): let a(i:ℕ)(p:Fin w) := atOne (discrete (r i) (Q p)) 0
       Tendsto (fun i=> (η i) (P.tuneK (lovely (a i) Z (Twah.letters w) (r i)))) atTop (𝓝 (Twah.witness Z (Twah.letters w) (fun i:Cellz (Fin w)=> Q i.1) 0)):=by
 intro a; let f(y:Cellz (Fin w)):= Q y.1
 let a':=fun (i:ℕ)(p:Fin w)=> Twah.homestead f (r i) p 0
 have he(i:ℕ)(x:Cellz (Fin w)) : sitesX (a i) x = sitesX (a' i) x:= by rw [show a' i= _ from (show _=fun p=>homestead f (r i) p (0:Fin w→DirSpin) from rfl), installed_home]; rcases x with ⟨x,b⟩; cases b<;> rfl
 have hs:riseUp a r f:= fun v=> (riseHome r f A.eager 0 v).congr fun i=> congrArg (riseX (r i)) (he i v).symm
 have ht:Twah.plateau a f:=fun x y g=> (homeHave r f (0:Fin w→DirSpin) x y g).mono fun i h=> (he i x).trans (h.trans (he i y).symm)
 exact (Prototype.rightRide A Z f a 0 (Eventually.of_forall fun i=> rfl) hs ht (Eventually.of_forall fun i j=> Nat.zero_le _) h u 3).congr fun i=>P.single_agrees 3 3 x (c i) _
omit A h u
lemma local_flat (z:Lead.Clan)(D: Gaia) : Twah.witness (fun i:Fin 1=> z) (Twah.letters 1) (fun _:Cellz (Fin 1)=> D) 0=0:=by
 rw [show Twah.letters 1 =[0] from rfl,chorus2,lyric,Cordial.billX]; simp [Onyx.pencil] -- tune
variable (y z: Gaia) (d':y (3:Axis) < z (3:Axis))
include A h u
lemma current_mean: Tendsto (fun i=> (η i) (P.equinox Z (Ft y i) (r i))) atTop (𝓝 0):=by
 let f:= fun (_:Fin 1)=>y
 have hv := one_bra A h u f (fun _=> Z); rw [show Twah.witness (fun i:Fin 1=>Z) (letters 1) (fun i : Cellz (Fin 1)=> f i.1) (0:Fin 1→DirSpin) =0 from local_flat Z y] at hv
 exact hv.congr fun i=> congrArg (η i) (P.songsAg _ (Gemini.flourish (R:=r i) ..) (mul_one _)) -- args?

local notation "Ξ" => zephyr y y z z
local notation "f" v:max i:max a:max => P.centeredSun x (c i) (P.equinox a (Ft v i) (r i))
local notation "F@" i:max a:max=> P.equinox Z (Ft a i) (r i) -- hygiene
variable (W:Lead.Clan)
lemma bra_value :
 Tendsto (fun i=> (η i) ((f y i Z)*(f z i W))) atTop (𝓝 (Twah.witness ![Z,W] (Twah.letters 2) (zephyr y y z z) 0)):=by
 let P':= ![y,z]; let d : Cellz (Fin 2)→ Gaia:= fun x=>P' x.1; have hd : d=Ξ:=by ext1 x; rcases x with ⟨x,b⟩; cases b<;> rfl
 have hn:Tendsto (fun i=> (η i) (P.equinox Z (Ft y i) (r i)* P.equinox W (Ft z i) (r i))) atTop (𝓝 (Twah.witness ![Z,W] (letters 2) d 0)) := (one_bra A h u P' ![Z,W]).congr fun i=> congrArg (η i) (P.songsAg _ ((Gemini.flourish (R:=r i) (atOne (Ft y i) 0) Z).mul (Gemini.flourish (atOne (Ft z i) 0) W)) (congrArg ((atOne _ 0).groundWord (r i) Z * ·) (mul_one ((atOne _ 0).groundWord (r i) W)))) -- tune
 rw [hd] at hn; simp_rw [cent_sun]; convert hn.sub ((current_mean Z A h u y).mul (current_mean W A h u z)) using 1; simp
omit A h u
lemma bra_priced :
 Twah.witness ![Z,W] (Twah.letters 2) (zephyr y y z z) (0:Fin 2→DirSpin) = if Z=W then numberX Z*(kP20 (z-y))^2 else 0:=by
 have he(i:Fin 2) : Ξ (i,false)=Ξ (i,true):= rfl
 have hf(i:Fin 2)(Z:Lead.Clan): lyric (Ξ) 0 Z i=0:=by unfold lyric; rw [Cordial.billX,← he]; simp [Onyx.pencil]
 rw [show Twah.letters 2= [0,1] from rfl]; split_ifs with v
 · subst W; rw [show (![Z,Z] : Fin 2→Lead.Clan)= fun _=>Z from funext fun i=>by fin_cases i<;> rfl,chorus4,hf,hf]
   unfold Cordial.surprise
   rw [zero_mul,zero_add]; let Dt:= kP20; change numberX Z*(- Dt (y-z) * Dt (z-y))= _; rw [show Dt (y-z) = -Dt (z-y) from neg_sub z y ▸ k_flip _]; ring -- Dt z hy?
 rw [witness_pair_other _ _ _ (by exact v),hf,hf,mul_zero]
include d'
lemma handed_light : numberX Z*(kP20 (z-y))^2 ≠0:=by
 have hx: z-y≠0:= by intro p; exact d'.ne ((congrArg (fun x:Gaia=> x (3:Axis)) (sub_eq_zero.mp p)).symm)
 refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
 · unfold numberX dimf; split_ifs <;> norm_num
 unfold kP20 Onyx.pencil; rw [Matrix.smul_apply,quaternion]
 apply smul_ne_zero; · apply ne_of_gt; positivity
 intro p; have h:= congrArg Complex.re p; simp at h; linarith
include A h u
local notation "Hm" i:max => P.ticketRank x (c i) (fun k=>f y i k) (fun k=>f z i k)
lemma mature_six : ∀ᶠ i:ℕ in atTop, ReadsSix (P.ticketRank x (c i) (fun k=>f y i k) (fun k=>f z i k)):=by
 let D:= Matrix.diagonal (fun Z:Lead.Clan=> numberX Z*(kP20 (z-y))^2)
 have ht:ReadsSix D:= ⟨by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>handed_light i y z d'),fun i=> Matrix.diagonal_apply_eq _ _ |>.trans_ne (handed_light i y z d')⟩
 have he:Tendsto (fun i=> (Hm i)) atTop (𝓝 D):=by
    refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr fun j=> ?_)
    have hx:= bra_value i A h u y z j; rw [bra_priced] at hx; exact hx -- ite simp
 exact he.eventually (readsSix_open.mem_nhds ht)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
