import YM.CF.Floe.Meat
import YM.CF.Jet.Balm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
open Jet
open scoped ContDiff
set_option synthInstance.maxSize 16000
variable {m B N: Side}{n:ℕ}{K b c d r:ℝ}
local notation "Ψ"=> CSide m B
local notation "S₀"=>Op (SpinIdx× SU.Slot)
lemma postT(n:ℕ)(p:1≤K)(D:ℝ)(k:0 ≤D):∃ C:ℝ,0 ≤C∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](N:Side)(U:E→Tenant.Input N) (x:E), TransK n (fun x=>(U x).1) x K→ (∀ j a, Allows n (fun x=>(U x).2 j a) x D) → Allows n (fun x=>skin (U x)) x C:=by
 let T(z:Op SU.F):H0:= (1:Op SpinIdx) ⊗ₖ SU.triple z; have hx: ContDiff ℝ (↑n:WithTop ℕ∞) T:=by
    apply matt; intro i j; exact ContDiff.mul contDiff_const ((elem i.2 j.2).comp trie)
 let Q:=zero_le_one.trans p; obtain ⟨a,g,h⟩:= compact_allow n Q T hx; obtain ⟨d,v,z⟩:=compact_allow n k localPair cc_full; let A:=composeCost n a K; let Y:= composeCost n d D; let R:=starL' ℝ (A:=H0); let V:=max A Y; have hV:0 ≤ V:=le_max_of_le_left (by unfold A composeCost; positivity)
 let W:=max V (‖R.toContinuousLinearMap‖*V); have hW:0 ≤ W:= le_max_of_le_left hV
 refine ⟨W,hW,fun E _ _ N U x g F=> ?_⟩
 have ht(q:E→H0)(l:Allows n q x V):Allows n (fun x=>vow (q x)) x W:=by
    apply allows_pi hW; intro i; cases i; exact (l.linear R.toContinuousLinearMap le_rfl).mono (le_max_right ..); exact l.mono (le_max_left ..)
 have hv:Allows n (fun t=>(skin (U t)).1) x W:= allows_pi hW fun i=> ht _ (((h _ (g i).value).comp (f:=fun x=> SU.fund ((U x).1 i)) (g i)).mono (le_max_left ..))
 let f(t:E)(h:Bool)(z:Site N):=vow (localPair ((U t).2 h z)); have hp:Allows n f x W:= allows_pi hW fun i=>allows_pi hW fun b=> ht _ (((z _ (F i b).value).comp (f:=fun x=>(U x).2 i b) (F i b)).mono (le_max_right ..))
 exact hv.pair hp
lemma markA(n:ℕ)(p:1≤K)(B:Side):∃ C:ℝ,0 ≤ C∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](m:Side)(T S:Sq)(U:E→Skin m B)(A:E→ArrayF m)(x:E),TransK n U x K →arr n A x K →∀ (v:Hub m)(e:ℝ)(t: Phase.Zone),T∈ Phase.zone t→S∈ Phase.zone t→ Room B e→Guard (U x) e → Cube.Verified m B margin (U x) (A x) t → Allows n (fun x=>skin (stationP m B T S v (U x) (A x))) x C:=by -- tune
 obtain ⟨a,y,g⟩:=breezeT n (zero_le_one.trans p) B; obtain ⟨d,h,X⟩:=box_k n y; obtain ⟨C,x,u⟩:=postT n p _ h
 refine ⟨C,x,fun E _ _ m T S U V x t A v e q pQ q' pv r vR=>?_⟩
 let b(x:E):= stationP m B T S v (U x) (V x); change Allows n (fun x=>skin (b x)) x C; apply u E _ b x
 · intro i; unfold b; cases v
   · exact t i
   rename_i v; simp only [stationP,twinR,replica]; split; exact t _; exact allows_const _ ((show ‖SU.fund 1‖=1 by rw [SU.fund_one]; simp).trans_le p)
 intro j i; have h(Y:Site (Domain m B))(H: Sq)(s:H∈Phase.zone q): Allows n (fun x=>paintV m B (U x) (V x) H Y) x d:=by -- infer
    let f(t:E):= paint m B (U t) (V t) H Y; have he:= g E m U V x t A H s.1 Y; have hw:= prism_nonzero _ s.1 pv.1 r vR s.2 pv.2.2.1 Y -- tune
    refine (X E f x he hw).germ ?_; filter_upwards [he.smooth.continuousAt.eventually_ne (norm_pos_iff.mp ((half_pos low_p).trans_le hw))] with x p; exact Brace.box_u p
 cases v <;> exact h _ _ (either_duo pQ q' j)
end YM.CF.Floe
