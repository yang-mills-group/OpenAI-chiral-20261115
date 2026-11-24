import GaugeFieldConstruction.MapleC
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
section
variable {K:Calibration}{n:Side}{I:Type*}[Finite I]{L: List I}
variable (S:I→Finset Cover)(o:I → Cover)(W:I→Family K)
noncomputable def drift (o:I → Cover)(W:I→Family K)(L:List I):List (Raft K I):= L.map fun i=>⟨o i,i,W i⟩
lemma drift_pay : wharf (drift o W L)=(L.map W).prod:=by unfold drift wharf; rw[List.map_map]; rfl
lemma drift_buoy (r:I→ℝ):buoy r (drift o W L)=(L.map r).prod:=by unfold drift buoy; rw[List.map_map]; rfl
lemma drift_σ {σ:Cover}{w:ℤ}(v:(L.map fun i=>atDeck n (o i)).Nodup): Vibro W o σ w n (drift o W L):=by
 constructor
 · intro a p; obtain ⟨b,u,rfl⟩:=List.mem_map.mp p; exact Sloop.first
 unfold drift; rw[List.map_map]; exact v
lemma drift_q {W':I→ℕ→Family K}(p:∀ i,BQueue (S i) (W' i) (W i)) :∃ T:Finset Cover, BQueue T (fun n=>wharf (drift o (fun i=>W' i n) L)) ((L.map W).prod):=by
 induction L with
 | nil=>exact ⟨∅,BQueue.stay InTest.one zero_lt_one pay_unit⟩
 | cons a L ih=> obtain ⟨T,t⟩:=ih; exact ⟨_, (p a).multiply t⟩
private lemma arrive (x:Cover):∃ c:ℕ,∀ (n:Side),c≤n.val →∀ i:Axis,-↑((More n).val:ℕ) < 2*x i ∧ 2*x i≤ (More n).val:=by
 let b:ℕ:= univ.sup (fun i=> (x i).natAbs)
 refine ⟨b+1,fun n e i=>?_⟩
 have p:(x i).natAbs≤ b:=le_sup (s:=univ) (f:=fun i=> (x i).natAbs) (mem_univ i)
 rw [show (More n).val=n.val*2 from rfl]; push_cast; constructor <;> omega
lemma big_drift (u:(L.map o).Nodup):∃ c:ℕ,∀ (n:Side),c≤n.val→ (L.map fun i=>atDeck n (o i)).Nodup:=by
 induction L with
 | nil=> exact ⟨0,fun n _=>List.nodup_nil⟩
 | cons a L ih=>
    obtain ⟨e,g⟩:=List.nodup_cons.mp u
    choose c h using fun i:I=> arrive (o i)
    obtain ⟨d,p⟩:=ih g
    letI:=Fintype.ofFinite I; let D:= univ.sup c
    have ht(i:I): c i≤ D :=le_sup (f:=c) (mem_univ i)
    refine ⟨max D d,fun n z => List.nodup_cons.mpr ⟨?_,p n ((le_max_right _ _).trans z)⟩⟩
    intro t; obtain ⟨i,f,b⟩:=List.mem_map.mp t
    have he:lift (atDeck n (o i))=o a:=lift_eq_iff.mpr ⟨b,h a n ((ht a).trans ((le_max_left _ _).trans z))⟩
    apply e (List.mem_map.mpr ⟨i,f,(lift_eq_iff.mpr ⟨rfl,h i n ((ht i).trans ((le_max_left _ _).trans z))⟩).symm.trans he⟩)
end
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(s:ℕ)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
variable {J:Type*}[Finite J]
variable {σ:Cover}{A:ℕ}{G:J→ℝ}{o:J → Cover}{F:J→ℕ→Family (tent Y H)}{f:J→Family (tent Y H)}{S:J→Finset Cover}
variable {L:List J}
include V Q
local notation "W₁" => westW Y A
lemma maple_price (u:chute Y σ)(pu:∀ j,BQueue (S j) (F j) (f j))(h:∀ j,Barn K W₁ σ (o j) (S j))(g:∀ j,0≤G j)(z:∀ j c, G j<c→ SnowPrice (i:=i) (k:=k) (a:=a) (b:=b) Y H s σ (o j) W₁ (F j) c)(v:(L.map o).Nodup) : ‖E s ((L.map f).prod)‖ ≤(L.map G).prod:=by
 have H₀ (c:ℝ)(u':0<c): ‖E s ((L.map f).prod)‖ ≤ (L.map (fun i=>G i+c)).prod:=by
    let G':J→ℝ:=fun i=>G i+c/2
    have p(i): G i<G' i:= lt_add_of_pos_right _ (half_pos u')
    obtain ⟨T,hq⟩:=drift_q (L:=L) S o f pu
    apply le_of_tendsto (hot_deck Y H V s Q _ T hq).norm
    let i':= fun r:ℕ=> π r
    have hp:Tendsto i' atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    obtain ⟨C,e⟩:=big_drift o v
    filter_upwards [hot_G Y H V Q s pu h (fun i=>(g i).trans_lt (p i)) (G':=fun i=>G i+c) (fun i=>add_lt_add_right (by linarith only [u']) _) (fun i=> z i (G' i) (p i)), hp.eventually (water_paid Y H σ u s A),eventually_nFar Y H s (σ:=σ) (W:=W₁) hp C] with y t ⟨n,s⟩ a
    exact (t n s _ (drift_σ _ _ (e n (a n s)))).trans_eq (drift_buoy ..)
 have hv(L:List J): Continuous (fun c:ℝ=> (L.map (fun j=>G j+c)).prod):=by
    induction L with
    | nil=> exact continuous_const
    | cons j L ih=> exact (continuous_const.add continuous_id).mul ih
 let d:ℝ→ℝ:=fun c=> (L.map (fun i=> G i+c)).prod; have ht:Tendsto d (𝓝[>] (0:ℝ)) (𝓝 (d 0)):=((hv L).tendsto 0).mono_left nhdsWithin_le_nhds
 have p:= ge_of_tendsto ht (((show ∀ᶠ x:ℝ in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin).mono H₀)) -- tune
 simpa[d] using p
#print axioms maple_price
end
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
