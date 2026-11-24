import YM.SU5.Reconstruction.Marque.Clipping
import YM.SU5.Reconstruction.Marque.Discharge
import YM.SU5.Reconstruction.Crease.Rounds
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
namespace Districts
open YM.Marque.Flow YM.Marque
local notation "j"=> YM.Marque.Flow.clock
local notation "ℌ"=> G₀ j -- allowed?
local notation "Ω"=> Ω₀ j
local notation "S"=> S₀ j
local notation "Φ"=>Sight Y H V G C a χ j
local notation "M"=> floor Y H V G C a χ j
lemma compactReel(u v:Axis→ℝ):IsCompact (Reel clock u v):= by
 let K'(x:Axis):Set ℝ:= if x=j then {0} else Icc (u x) (u x+v x)
 let Z:= Set.univ.pi K'; have h: IsCompact Z:= isCompact_univ_pi (show ∀ i, IsCompact (K' i) from (by intro i; unfold K'; split_ifs; exact isCompact_singleton; exact isCompact_Icc))
 rw [show Reel clock u v= WithLp.toLp 2 '' Z from ?_]; exact h.image (PiLp.continuous_toLp _ _)
 ext1 x; refine ⟨fun t=> ⟨x.ofLp,fun i _=>?_,rfl⟩,fun t=>?_⟩;
 · by_cases v:i=j;·subst i; simpa[K'] using t.1
   simpa[K',v] using t.2 i v
 obtain ⟨x,u,rfl⟩:=t; exact ⟨show x j=0 from (by simpa[K'] using u j (by simp)),fun i p=> show x i∈_ from (by simpa[K',p] using u i (by simp))⟩
noncomputable def parcel : Gallery ℌ S where
   Row := (Axis→Gt)× (Axis→Gt)
   hue uv:= setOf (Φ uv.1 uv.2)
   footprint uv:= Reel clock (fun i=>(uv.1 i:ℝ)) (fun i=>(uv.2 i:ℝ))
   close_footprint _:= compactReel ..
   shades m x p:=adjSight Y H V G C a χ F clock _ _ _ p
local notation "Κ" => parcel Y H V G C a χ F
local notation "N"=> (Κ).lobby
include F
lemma tile_align (u:Set E4): (Κ).tiles u=Wing Y H V G C a χ j u:=by
 ext1 x; refine ⟨fun t=>?_,fun t=>?_⟩;·obtain ⟨⟨q,b⟩,v,t,x,k,e⟩:=t; exact ⟨q,b,v,t,x,k,e⟩
 obtain ⟨x,y,z,v,q,d,t⟩:=t; exact ⟨(x,y),z,v,q,d,t⟩
lemma declared (V': Set E4): N V'=M V':= congrArg Auditorium (tile_align Y H V G C a χ F V')
omit F
variable (z:Axis)(b:clock≠z)
local notation "L"=> Flare Y H V G C a χ F clock z b
local notation "Β"=> pinpoints Y H V G C a χ clock z
local notation "Σ"=> Wedge clock z
open CrossedFrame
structure Bench where
  room : Hilbert
  Zed : Clasp room (G₀ j) (G₀ z)
  gaze : Quarter Y H V G C a χ clock z b.symm Zed
  funded : Creased Y H V G C a χ F clock z b
variable (uPrime:Bench Y H V G C a χ F z b)
local notation "T"=> uPrime.Zed
-- housing exact
noncomputable def layout : Chair N Ω z:= ⟨uPrime.room,G₀ z,T,L,Β,by rw [declared]; exact engaged Y H V G C a χ F clock z b T uPrime.gaze uPrime.funded⟩
include F uPrime
local notation "K'"=>layout Y H V G C a χ F z b uPrime
local notation "Ṁ"=>Picket.move clock z
local notation "ℶ"=> Picket.trans S
lemma reflectCons (W:Set E4):Conveys (K').mirror (N W) (N (BridgeClub.turn clock z '' W)):=by
    intro A B e; rw [declared,declared]; change Across (rain (L)) A B at e; rw [e.unique (rainAcross (L) A)]; exact reflection_cov Y H V G C a χ F clock z b W A
lemma turnsV(x:E4): Across (K').mirror (ℶ x) (ℶ (BridgeClub.turn clock z x)):=by
 rw [← orbitF Y H V G C a χ F clock z b]; exact rainAcross (L) (ℶ x) -- tune eta
lemma balance(t:ℝ)(A:(G₀ j).Op): Across ((K').boost t) A (ascend t T A):= by
 intro x; rw [Chair.bank, Chair.bank]; change (Picket.boost T t*A*star (Picket.boost T t)*Picket.boost T t) x=(Picket.boost T t*A) x; rw [mul_assoc (Picket.boost T t*A),(Picket.boost_pays ..).1,mul_one]
lemma real_balance : Gallery.Authenticates Κ Ω z b.symm K':= by
 refine ⟨fun x=> ?_,fun t=>?_,fun t x=>?_,fun t q A q' A' r=> ?_⟩
 · rw [mover_at]; exact compass_origin ..
 · rw [Chair.bank]; exact uPrime.gaze.vacuum.2 _
 · intro i; rw[Chair.bank,Chair.bank]; exact DFunLike.congr_fun ((uPrime.gaze.spins t).2 x).symm i
 rw [declared] at q'; have h:= (transported_room Y H V G C a χ F clock z b T uPrime.gaze uPrime.funded t q true A).1 (show A∈ M (strace q (Wedge clock z)) from q');
 rw [eitherShift] at h; rw [declared,r.unique (balance Y H V G C a χ F z b uPrime t A)]; exact h
 exact b.symm
end Districts
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
