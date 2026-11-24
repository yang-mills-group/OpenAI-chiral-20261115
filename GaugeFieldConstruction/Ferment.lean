import GaugeFieldConstruction.Faing
import YM.CF.Floe.Paid
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedVariables false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r a v e:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=>CSide m B
open Floe Tenant Celeb Dial
lemma utheta_j{p:0<d}:Continuous (uθ (N:=N) · p):=by
 refine Continuous.subtype_mk (Continuous.comp (show Continuous (skin (N:=N)) from ?_) (show Continuous (Subtype.val:Own N→Tenant.Input N) from continuous_subtype_val)) _
 unfold skin; have hd:Continuous vow:= continuous_pi fun i => by unfold vow; split <;> fun_prop
 refine Continuous.prodMk (continuous_pi fun i=> ?_) (continuous_pi (fun i=>continuous_pi fun j=>?_))
 · let F(g:SU.E):=Lat.color SU.matter g; have hv:Continuous F:= by
      refine continuous_matrix fun i j=>?_ ; exact continuous_const.mul (SU.matter_cont.matrix_elem i.2 j.2)
   exact hd.comp (hv.comp ((continuous_apply i).comp continuous_fst))
 exact hd.comp (localPair_cont.comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_snd)))
abbrev stK(x: Pantry m B):=stationP m B (stick 0) (stick 0) none x.1 (slot m x.2)
variable (H: Room B e)
def porter(x:Pantry m B)(p:x∈ Lobby m B e):Own Λ:= ⟨stK x, Phase.drives H (lobby_G p).1 (r:={0}) (lobby_G p).2 (stick_in _ (mem_singleton_self _)) (stick_in _ (mem_singleton_self _)) (by rw [sub_self,norm_zero]; positivity) none⟩
-- def H omitted capture issues? tune
abbrev CiteT (K c d:ℝ)(B:Side):Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m:Side)(V:E→ Skin m B)(x:E)(y:Cue m),Guard (V x) d →ZeroF m B (V x) y → TransK 7 V x K→Allows 7 (fun i=>skin (stK (V i,y))) x c
include H
lemma Staff (p:1≤K):∃ c:ℝ,0≤c∧ CiteT K c e B:=by
 obtain ⟨C,q,T⟩:=Floe.markA 7 p B -- tune spelling
 refine ⟨C,q,fun E _ _ _ m V x y t u v=> ?_⟩
 exact T E m (stick 0) (stick 0) V (fun _=>slot m y) x v (fun i=>allows_const _ ((vote_unit _).trans_le p)) none e {0} (stick_in _ (mem_singleton_self _)) (stick_in _ (mem_singleton_self _)) H t u -- check Lore order
abbrev bills(d:ℝ)(p:0<d)(A: Kelp (CSide m B) d→ Op (Model (CSide m B))) (U: Pantry m B): Op (Single Λ):= portW (helix Λ).symm (accessK m B (stick 0) (stick 0) none U.1 (slot m U.2) (fun x=> A (uθ x p)))
lemma bills_eq {A: Kelp (CSide m B) d→ Op (Model (CSide m B))} (p:0<d)(U:Pantry m B)(u: U∈ Lobby m B e): bills d p A U=portW (helix Λ).symm (A (uθ (porter H U u) p)):=by unfold bills; rw [entrance (show TenantK (stK U) from (porter H U u).property)]; rfl -- tune infer
variable {T V: Tag (ku (N:=CSide m B) (a:=d))} {A: Kelp (CSide m B) d→ Op (Model (CSide m B))}
variable {W: Toll (Model (CSide m B))}{S: Stamp m B}
local notation "vW"=> (8*B.val)
local notation "hfS"=>foam _ vW S
variable (t:Suite (badge _) T V S W A)(p:0<d) (C:b≥ 0)(D:CiteT K b e B)
local notation "Hfreq"=> helix Λ
lemma only_angle (x:Pantry m B)(u:x∈ Lobby m B e)(y:Pantry m B)(v:y∈ Lobby m B e)(g: Agrees (foam _ (8*B.val) S) x.1 y.1)(h:Phase.Sample.AgreeF (complexA m B (foam _ (8*B.val) S)) x.2 y.2): (ku (N:=CSide m B) (a:=d)).eval S (uθ (porter H x u) p) (uθ (porter H y v) p)=0:=by
 rw [Floe.moment]; apply station_read S none (stick 0) (stick 0) (fun i j k=>g i (fins S j) (fins S k)) trivial ?_
 intro i p'; exact h i.1 (chaps S (mem_product.mp p').1) -- tune slot second
include t C D
lemma portKa (i j: Single Λ): Ka K 7 e (foam _ (8*B.val) S) (fun x=> bills d p A x i j) (Floe.phiN 7 b d*W (Hfreq i) (Hfreq j)):=by -- replace spelling
 let l:=helix Λ i; let r:=helix Λ j; let g(k):=A k l r; let u:= W l r
 let E':=t.expo l r
 have hb(k): ‖g k‖ ≤ u:= E'.bounded k
 have hv(x: Pantry m B)(hp:x∈ Lobby m B e): bills d p A x i j=g (uθ (porter H x hp) p):=by rw [bills_eq H p x hp]; rfl
 have hx: 0 ≤ phiN 7 b d:=by unfold phiN composeCost; positivity
 refine ⟨mul_nonneg hx E'.positive, ?_,fun x u y v f l=> ?_,fun E _ _ _ F x y px h=>?_⟩
 · apply continuousOn_iff_continuous_restrict.mpr
   let Bv(y:(Lobby m B e)):=porter H y.val y.property
   have he:Continuous Bv:=by
     refine Continuous.subtype_mk ?_ _
     refine (dress (stick (0:Row)) (stick 0) ({0}:Phase.Zone) (stick_in _ (mem_singleton_self _)) (stick_in _ (mem_singleton_self _)) none H).comp_continuous (f:=fun i:(Lobby m B e)=> (i.val.1,slot m i.val.2)) ?_ ?_
     · exact (continuous_fst.comp continuous_subtype_val).prodMk ((slot_cont m).comp (continuous_snd.comp continuous_subtype_val))
     intro x; exact lobby_G x.property
   exact ((E'.connected.comp (utheta_j)).comp he).congr (fun y=> (hv _ y.property).symm)
 · rw [hv x u,hv y v]; refine sub_eq_zero.mp (norm_le_zero_iff.mp ?_)
   exact (E'.variation _ _).trans_eq (by rw [only_angle H p x u y v f l,mul_zero])
 let Y(z:E):=stK (F z,y); have hp:∀ᶠ z in 𝓝 x,(F z,y)∈Lobby m B e:= ((cliff_n h).prodMk (g:=fun _=>y) continuousAt_const).tendsto.eventually (lobby_o.mem_nhds px)
 have Ht:= Floe.painV g p (t.fuel l r) E'.connected hb x Y (hp.mono fun i p' => ((porter H (F i,y) p').property)) (D E m F x y (lobby_G px).1 (lobby_G px).2 h)
 apply Ht.germ; filter_upwards [hp] with i p; rw [hv _ p]; exact dif_pos (show _ ∈ Kelp (CSide m B) d from (uθ (porter H (F i,y) p) ‹0<d›).property)
end YM.CF.XGarden
end
