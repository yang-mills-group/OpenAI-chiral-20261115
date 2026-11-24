import YM.CF.BProof.Mote.Polar
import YM.CF.Bloom.Flux
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
variable {N P:Side}(G:Ratio N P)(j:ℕ) (Q:SpaceM)(M:Male)
open TripD
variable (i:Axis) (X:Nom N P) (v:Odd G.count.val)
-- fine reach shell for true Gauge/support uses BOTH endpoints. R Fine Halo = all arrived or consulted gauge. use radius 2*K.
abbrev reach (G:Ratio N P)(W:Support (More N))(K:ℕ):= halo (2*K) (W.image (ratio G).embed)
variable {W:Support (More N)}{k:ℕ}
lemma mfree {S:Finset m}{x:Ket m}(p:acts (cutM S) x=x){i:m}(t:x.ofLp i≠0):i∈S:=by by_contra h; exact t (by nth_rw 1 [←p]; rw [cut_apply,if_neg h])
lemma column_w (b:Bool){x:Ket (Single N)}(p:acts (cutM (modes W)) x=x)(l:Iota G)(q:(humP G Q b x).ofLp l≠0): (portico G l.1)∈ W.image (ratio G).embed:=by
 have hx:acts (cutM (modes W)) (click Q b x)=click Q b x:= shine p (belt_reach Q W b)
 by_cases h:l∈ lows (patchQ G); swap; · exact (q (basin _ _ l h)).elim
 obtain ⟨i,-,rfl⟩:=Finset.mem_map.mp h; have hp:(humP G Q b x).ofLp (patchQ G i)=(click Q b x).ofLp i:=by unfold humP; rw [←seamK, trails]
 rw [hp] at q; exact mem_image_of_mem _ ((mem_modes ..).mp (mfree hx q)) -- tune
lemma arriveD (j:Single P): arrive G ((switchG G).symm j).1=node j.1.1:= by obtain ⟨i,hi⟩:= (switchG G).surjective j; rw [←hi,Equiv.symm_apply_apply]; rfl
include v
lemma carrierL (g:SetK j G.count k)(b:Bool){x:Ket (Single N)}(p:acts (cutM (modes W)) x=x) (T:Bkg (More P)): acts (cutM (modes (reach G W (units G.count k)))) (songL G j M Q b T x)=songL G j M Q b T x:=by -- tune
 let S:= humP G Q b x; let F:=turret G j M T; let K:=units G.count k; let Y:=acts F S; let V:= (switchG G).symm; let U:=modes (reach G W K); change acts (cutM U) _=_; apply PiLp.ext; intro l; rw [cut_apply]; by_cases h:l∈U; rw [if_pos h]
 rw [if_neg h]; symm; unfold songL; rw [seamK]; change Y.ofLp (V l)=0; rw [show Y.ofLp (V l)=_ from act_at F S (V l)]; apply sum_eq_zero; intro r _; by_cases e:S.ofLp r=0; rw [e,mul_zero]
 have he:= column_w _ Q b p r e; have ht:K< separation (arrive G (V l).1) (portico G r.1):= lt_of_not_ge (fun q=> h ((mem_modes ..).2 (halo_spec.mpr ⟨_,he, (by rw [←arriveD G l,separation_comm]; unfold V at q; omega)⟩))); dsimp only; rw [show F (V l) r=0 from congrFun ((affordable G j v g M (V l) r).vista ht) T,zero_mul]
lemma song_c (g:SetK j G.count k)(b:Bool)(x : Ket (Single N)) : Continuous fun U:Pane P=>songL G j M Q b U x:=by unfold songL; exact ((trailK _).continuous_of_finiteDimensional.comp ((acts_cont.comp (turbine G j v g M)).clm_apply continuous_const))
lemma reach_p (g:SetK j G.count k)(b:Bool){x:Ket (Single N)}(p:acts (cutM (modes W)) x=x) : LocalOn (reach G W (units G.count k)) (fun U:Pane P=>songL G j M Q b U x):=by
 intro U V h; unfold songL; apply congrArg; apply PiLp.ext; intro i; rw [act_at, act_at]; refine sum_congr rfl ?_; intro l _; let z:=humP G Q b x; by_cases e:z.ofLp l=0; change _*z.ofLp l=_*_; rw [show (humP G Q b x).ofLp l=0 from e,mul_zero,mul_zero]; -- tune
 have ht:= column_w G Q b p l e; dsimp only; rw [show turret G j M U i l= _ from (affordable G j v g M i l).localP U V (by apply agrees_mono h; intro y (hy:y∈_); exact (halo_spec ..).2 ⟨_,ht,hy⟩)]
end Leg
end YM.CF.BProof.Bide
