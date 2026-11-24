import Verses.Oak
import Verses.Policy
import Verses.Bramble
import YM.SU5.Relativistic.Rebuke
import YM.CF.BPress.Spin.Touches
import Verses.Checkup
import YM.CF.Cubes.Inside
import YM.Work.E08
/-!
# One frame from positive curvature bound on the actually paid sites.
Use Work.E08 axial coarse estimate (works here directly on the gauge grid),
then shift to fixed continuous stencil rather than picking a frame measurably. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate.Pannier
open Work.E08
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
open YM.Pressure YM.Gleam YM.Gleam.Luster YM.Gleam.Luster.Almanac Grade
namespace Flint
open Papyrus.Franc.Verses CF.Window Scree
attribute [local instance] opCStarAlgebra
abbrev markXcost (j:ℕ)(W:ℕ):ℝ:= 4*((j+4)*2+1:ℕ)^4*((W+1)+(W+1)+1:ℕ)^4 * (2*(W:ℝ)+1)^4 -- mixed types? first 4s infer Nat? annotate
abbrev orderT (a Q k:ℝ)(L:Side)(x:ℝ):= (2*Real.exp (-(a*radiusB x))+(radiusB x:ℝ)*4*sticker (wallsF L x) (sax x)/k)*Q
lemma sticker_nonneg (r:ℕ){t:ℝ}(p:0≤t) :0≤ sticker r t:=by unfold sticker Circa; have h:=BPress.Spin.sphereRate_cost.positive; positivity
lemma sticker_tile (L:Side) : Grade (-2/5) (fun x=> sticker (wallsF L x) (sax x)):=by
 unfold sticker Circa; skip
 have hg:=caps_grade L
 let a(x:ℝ):ℝ:=wallsF L x; let u:=BPress.Spin.sphereRate; let K:ℝ:=Fintype.card PlaqAxes
 have ht: Grade ratioV a:=hg
 have h0:= (block (1:ℝ)).grow (b:=ratioV) (by norm_num [ratioV,tauA])
 let f(x):=8*a x+1; have hf:Grade ratioV f:=(ht.scaleB 8).plus h0
 let g(x):=2*(a (x:ℝ)+1)+1; have he:=Grade.plus (Grade.scaleB 2 (Grade.plus ht h0)) h0
 let g'(x):=(16*(g x)^5)*K
 have hg':Grade (ratioV*5+0) g':=by apply Grade.mul (Grade.scaleB (16:ℝ) _) (block K); simpa using he.pwr 5 -- Nat coercions
 change Grade _ (fun x=>u*(f x*g' x*sax x)); exact ((((hf.mul hg').mul sax_b).scaleB u).grow (by norm_num [tauA,ratioV]))
lemma grade_order (L:Side)(a Q k:ℝ)(p:0<a) : Grade (-2/5) (orderT a Q k L):=by
 have he:= trail_b p; let K:=(-2/5:ℝ); have hh:∀ x,trail a (radiusB x)=Real.exp (-(a*radiusB x)):=by intro i; unfold trail; ring_nf
 simp_rw [hh] at he
 have hx:= ((radiusBill.mul (sticker_tile L)).scaleB (4/k))
 apply Grade.cash ((((he.scaleB 2).grow (b:=K) (by norm_num [K])).plus (show Grade K _ by simpa only [zero_add] using hx)).scaleB Q)
 filter_upwards with x; apply le_of_eq; congr 1; unfold orderT; ring

-- fixed tile geometry, Loom flag cardinal, column bill
lemma projector_charge {N:Side}{u t:ℝ}{j:ℕ}{A0:Loom N}(g:Roof N u t j A0) (x:Orbit N)(m k w r:ℕ)(v:ℝ)(hv:0≤v)(hu:v≤u)(hf:r+m+1=w){c:Side}(R':Lattice.Ratio c (More N))(s:R'.count.val=2*w+1)(d:2*(w+1)<(More N).val){ρ:ℝ}(fe:((2*w+1:ℕ):ℝ)^4-((2*r+1:ℕ):ℝ)^4 ≤ ρ*((2*w+1:ℕ):ℝ)^4)(M:Tulip.Male){a C δ:ℝ}(h:0<a)(p:0<C)(H:0<δ)(K:Checkers.Sow 4 N a C δ)(f:t≤δ) :
    let Q:=spar 4 M (A0 x); let Z:=spar 4 M (1:Pane N);
    ∃ l:Seat N→ E, entryBudget (spar 4 M (gauge l (A0 x))-Z) ≤ ((2*Real.exp (-(a*m))+m*4*sticker w v/δ)*C)*(180*N.val^4)+(2*C*180)*(ρ*(More N).val^4+ (4*((j+4)*2+1:ℕ)^4 :ℕ)*((w+1)+(w+1)+1:ℕ)^4* (2*(w:ℝ)+1)^4* (flakes v x.1)):=by
 intro Q Z
 let y:=flakes v x.1
 let X:= A0 x; let D':=(4*((j+4)*2+1:ℕ)^4*((w+1)+(w+1)+1:ℕ)^4:ℕ)
 have he:( (Lattice.halo (w+1) (RG.flags v X)).card:ℝ) ≤ y*D':=by
    have he:= grease_f g x hu (w+1) 1; change (halo _ (RG.flags v (pull 1 0 X))).card≤_ at he; rw [show Lattice.pull 1 0 X=X from ?_] at he
    · exact (Nat.cast_le.mpr he).trans_eq (by unfold y D' flakes; push_cast; ring)
    rw [Lattice.pull_one]; ext i; simp [Lattice.translate]
 obtain ⟨S,l,hL,V⟩:= wallMaps R' s d X v (sticker w v) (fun i e=> stampG_prec _ hv d le_rfl _ _ e) hf.le he
 have hs:(Sᶜ.card:ℝ)≤ ρ*(More N).val^4+y*D'*(2*w+1:ℝ)^4:=by
    refine V.trans (add_le_add ?_ ?_); swap
    · have hv:0 ≤ y*D':=by unfold y flakes; positivity
      have hx : r≤w:=by omega
      gcongr
    have hU: ((More N).val:ℝ)=(c.val:ℝ)*(2*(w:ℝ)+1):=by exact_mod_cast (R'.exact_size.trans (congrArg (c.val*·) s))
    apply (mul_le_mul_of_nonneg_left (show (2*w+1:ℝ)^4-(2*r+1:ℝ)^4≤ ρ*(2*w+1:ℝ)^4 by exact_mod_cast fe) (by positivity : 0 ≤ (c.val:ℝ)^4)).trans_eq
    rw [hU]; ring
    -- V has r not w. adapt
 let T:=spar 4 M (gauge l X); let P:=univ.filter (fun i:Single N=> node i.1.1∈ Sᶜ)
 let J:=2*C; let U:= (2*Real.exp (-(a*m))+(m:ℝ)*4*sticker w v/δ)*C; have h0:0≤ U:=by unfold U; have h:=sticker_nonneg w hv; positivity
 have ht: Guard (gauge l X) δ:=(Guard.cov (g.paid x) l).shrink f
 have hx:Guard (1:Pane N) δ:=guard0 H.le
 refine ⟨l,?_⟩; unfold entryBudget; rw [sum_comm]; let F(i:Single N):=∑ j:Single N, ‖(T-Z) j i‖
 change ∑ i,F i≤_
 have hF(i:Single N): F i≤ U+ if i∈P then J else 0:=by
    split_ifs with wP
    · apply le_trans (b:=J) ?_ (le_add_of_nonneg_left h0); have he:∑ j:Single N,‖T j i‖ ≤ C:= K.daylight false M _ ht i
      have hp:∑ j:Single N,‖Z j i‖ ≤ C:=K.daylight false M _ hx i
      unfold F; calc
       _ ≤∑ j:Single N,(‖T j i‖+‖Z j i‖):=sum_le_sum (fun j _=>norm_sub_le ..)
       _ ≤ _:=by rw [sum_add_distrib]; unfold J; linarith only [he,hp]
    rw [add_zero]; let A:Op (Single N):= Matrix.of (fun j k=> if node k.1.1∈S then (T-Z) j k else 0); have hp: condor A U:= K.cross false M _ _ ht hx S _ m (sticker_nonneg w hv) hL A (fun j k=>by unfold A; rw [Matrix.of_apply]; split_ifs with hh; exact Or.inr ⟨hh, le_rfl⟩; tauto)
    rw [show F i=∑ j:Single N,‖A j i‖ from ?_]; exact hp i
    exact sum_congr rfl (fun j _=>by unfold A; rw [Matrix.of_apply,if_pos (show node i.1.1∈ S from (by simpa [P] using wP))])
 apply (sum_le_sum (fun i _=> hF i)).trans
 rw [sum_add_distrib, sum_ite,sum_const_zero,sum_const,sum_const,add_zero,filter_mem_eq_inter,univ_inter,card_univ]; -- tune casts
 have hG: (P.card:ℝ) ≤ (Sᶜ.card:ℝ)*180:=by unfold P; exact_mod_cast (sit_card Sᶜ)
 simp only [nsmul_eq_mul,J,Pic.units_t]; -- shouldn't unfold P
 unfold y U D' at *; push_cast at *; nlinarith only [mul_le_mul_of_nonneg_right hG (show 0≤ 2*C by positivity),mul_le_mul_of_nonneg_left hs (show 0≤ 2*C*180 by positivity)]
end Flint
end YM.CF.Pannier.Chancel
