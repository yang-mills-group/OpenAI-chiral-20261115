import YM.CF.Swell.Pole
import YM.CF.Chaff.Hub
import YM.CF.Swell.Pod
import YM.CF.Sour.Lumen
import YM.CF.Nor.Pile
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
variable {N B m:Side}{r:ℕ}(k:ℕ) {a b c d t e:ℝ}
-- per support trace, compress down.PAYS polynomial power of S not inflated Halo from P.S
variable {P:BudgetPoint}{L:Scree.Loom N}(U:Roof N a e r L)(h:0<e)(hp:P.threshold≤ a)(hT:r+10≤ P.B)(hP:3 ≤ P.B)(hpκ:cipherK r≤ 5*P.B)(hx:HopeT e b t P.order)(hW:P.threshold ≤ t)
variable (S:Support (Cube.More N))(o: Seat N)(p:o∈ S)(X:Scree.Hub N)(xP:X.val.1=o)(p': X.val.2=Lattice.halo P.B S)
variable (C:Toll (Single N))(F:Raw (Openc (Cube.More N) e) (Single N))(g:Suite (badge _) (bail N e) (bail N e) S C F)(T:Ids N)
open Ione Chaff
include hp hT U g p' p
private lemma view_u(V Y:Pane N)(q:V∈ Sour.σX P (lagE X) ∅)(t:Y ∈ Sour.σX P (lagE X) ∅)(k:Agrees S V Y): spineH U h F (V,T)=spineH U h F (Y,T):=by
 let hx : Lattice.halo (r+10) S⊆(lagE X).val:= (show _⊆X.val.2 from p' ▸ (Corona.halo_mono hT (Subset.refl _))); apply congrArg Matrix.trace; apply pact_p h U g; intro i j t'; exact (fern U hp S hx V q i j rfl T).trans ((k i j t').trans (fern U hp S hx Y t i j rfl T).symm)
abbrev rGain(P:BudgetPoint)(S: Support (Cube.More N))(C:Toll (Single N)):= liftR P S 0 (ledgerV C) -- STRETCH.P ratio factor <= nfact times.
include U h hx hW hP hpκ xP
private lemma gear_V(i:Pane N)(x:i∈σX P (lagE X) ∅)(j: Tulip.Single N) :let M:=rodV P o S (∅:Support (Cube.More N)); let Y:=fun v:tangD N=>F (roller h U (pressQ P (∅:Support (Cube.More N)) i (M v),T)); Allows P.order (fun v:tangD N=>Y v j j) 0 (composeCost P.order (C j j) (surgeL P S 0)):=by
 intro M Y; have he:= Rill.earn_b h U hp g hx (i,T) (lagE X) (show _⊆ X.val.2 from p' ▸ (Corona.halo_mono hT (Subset.refl _))) hW (show Lattice.halo (cipherK r) ∅⊆ _ from by simp [Lattice.halo]) hpκ hP x (show (∅: Support (Cube.More N))⊆∅ from le_rfl) j j
 let V':tangD N→ℂ:=fun a=> F (roller h U ((pressQ P (∅:Support (Cube.More N)) i a,T):Orbit N)) j j; have hp:Allows P.order V' (M 0) (C j j):=(map_zero M).symm ▸ he
 apply hp.comp; exact allows_linear (lens_x P o S ∅ 0 p) (le_of_eq_of_le (by rw [M.map_zero,norm_zero]) (zero_le_one.trans (rootA P o S 0 p))) -- signature rootA p arg
abbrev cut_L(P:BudgetPoint) (c t:ℝ):ℝ:=composeCost P.order c t
lemma priceL (V:Pane N)(tV:pingS P.threshold X.val.2 V): let F':=rent_Φ (P:=P) U h X F T; Signs P X.val.1 (fun t:tangD N=> crumb (F' (RG.increment V t)).val ∅) (rGain P S C):=by
 intro E; rw [xP]; apply Prism.skills; let M:= rodV P o S (∅: Support (Cube.More N)); let Φ:=Sour.σX P (lagE X) ∅; have hY: V∈Φ:=⟨by rw [sdiff_empty]; exact tV, empty_subset _⟩
 let L':= fun t:tangD N=> pressQ P (∅:Support (Cube.More N)) V (M t); let Y:=fun t=> F (roller h U (L' t,T)); let y:= fun t=>Matrix.trace (Y t); let f:=fun t=> crumb (E (RG.increment V t)).val (∅:Finset (Dwell N)); let K:= surgeL P S 0
 have hv(Y':Op (Single N)):Matrix.trace Y'=∑ j:Single N,Y' j j:=rfl; have hpA:Tendsto M (𝓝 0) (𝓝 0):=by simpa using M.continuous.tendsto 0
 have H: Allows P.order y 0 (∑ i: Single N,composeCost P.order (C i i) K):= allows_sum fun i _=> gear_V U h hp hT hP hpκ hx hW S o p X xP p' C F g T V hY i -- fix shadow!
 refine (H.germ (f':=f∘ Prism.trunk P o) ?_ ).mono ?_
 · let G(u):=RG.increment V (Prism.trunk P o u);
   have hw:∀ᶠ u:tangD N in 𝓝 0,pingS P.threshold X.val.2 (G u):=Chaff.wind_p V _ tV
   have hZ:∀ᶠ u:tangD N in 𝓝 0,pingS P.threshold X.val.2 (L' u):=by rw [←show (X.val.2 \ ∅)=X.val.2 from Finset.sdiff_empty]; exact hpA.eventually (Vow.tick (P:=P) (Y:=∅) (D:=∅) (U:=V) hY.1) -- tune
   filter_upwards [hw,hZ] with t hx hk
   change Matrix.trace (Y t)= f (Prism.trunk P o t); rw [show f (Prism.trunk P o t)= spineH U h F (G t,T) from ?_] -- tune
   · apply view_u U h hp hT S o p X p' C F g T (L' t) (G t) ⟨by rw [sdiff_empty]; exact hk,empty_subset _⟩ ⟨by rw [sdiff_empty]; exact hx,empty_subset _⟩; -- loc_y
     have hpX(e:tangD N): openG P ∅ e=e:=by funext i; simp [openG,Lattice.halo]
     let R:= Vow.loc_y (U:=V) M rfl t; rw [hpX] at R; exact R
   change crumb (rent_Φ _ _ _ _ _ _).val _= _; rw [sketch U h hp hT S X p' C F g T (G t,T) hx]; simp [crumb,hollow]
 have hv:∑ i:Single N,C i i≤ Branch.ledgerV C:=sum_le_sum (fun i _=>single_le_sum (f:=fun j=>C i j) (fun j _=>g.nonn _ _) (mem_univ i))
 have hi: 1 ≤ K:= rootA P o S 0 p
 change _≤ composeCost P.order _ K; unfold composeCost; simp_rw [← sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv.trans (le_mul_of_one_le_left (sum_nonneg fun i _=>sum_nonneg fun j _=>g.nonn _ _) (by exact_mod_cast P.order.factorial_pos))) (by positivity)) (pow_nonneg (by linarith) _)
lemma helix_s(v:ℝ): PressB P X (rent_Φ (P:=P) U h X F T) v (rGain P S C):=by
 let k:=rGain P S C
 have he:0 ≤ k:=by unfold k rGain liftR composeCost; have h:0 ≤ ledgerV C:=sum_nonneg fun i _=>sum_nonneg fun j _=>g.nonn _ _; unfold surgeL; positivity
 let L':=fun i:Finset (Dwell N)=>if i=∅ then k else 0
 refine ⟨pond_L U h hp hT S X p' C F g T,fun i=>Flour.grainE.smul _, muskP U h hp hT S X p' C F g T,stampK U h hp hT S X p' C F g T, L',fun k=>by unfold L'; split; exact he; exact le_rfl,?_,?_⟩
 · intro i t j; unfold L'; split; next u=> subst j; exact priceL U h hp hT hP hpκ hx hW S o p X xP p' C F g T i t
   next w=> have hv(Y:Pane N):crumb (rent_Φ (P:=P) U h X F T Y).val j=0:=by simp [rent_Φ,crumb,hollow,Matrix.one_apply,w];
            simp_rw [hv]; exact Prism.hail norm_zero.le
 unfold L'; simp_rw [mul_ite,mul_zero]; simp [Scree.tariff,endL]; exact le_rfl
end YM.CF.Swell
