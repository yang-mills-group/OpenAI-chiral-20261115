import YM.CF.Font.Chin
import YM.CF.Thera.Ticket
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c f:Side}
abbrev FiX(n:Side):= Site (More n)
def place_x{x:Side}(i:Single x):FiX x:=node i.1.1
def dish(G:Ratio c f)(x:Single f)(y:Single c):=separation ((ratio G).parent (place_x x)) (place_x y)
def bolt (a:ℝ)(G:Ratio c f)(x:Single f)(y:Single c):ℝ:=Real.exp (a*dish G x y)
lemma dish_le (G:Ratio c f)(ho:Odd G.count.val)(x y:Site c)(i j:SpinIdx)(k l: SU.Slot)(b:Site G.count): dish G (switchG G ((x,(b,i)),k)) ((y,j),l)≤ 2*separation x y + 4:=by
 let A:= node x; let B:= node y; let v:=place_x (switchG G ((x,(b,i)),k)); let u:= place_x ((y,j),l); let R:= ratio G
 have hp: v=R.embed A+wrap _ (2 • lift b):= embed_node G ho ..
 have hh : separation (R.embed A) v ≤ 2*G.count.val:=by
   rw [hp, separation_comm, separation, add_sub_cancel_left]; apply Work.E01.pdist_wrap_le; rw [box_test];
   have h (z): - (↑(2*G.count.val):ℤ)≤ (2:ℕ) • lift b z∧(2:ℕ) • lift b z ≤ (↑(2*G.count.val):ℤ):=by have h:= lift_centers b z; simp only [nsmul_eq_mul,Nat.cast_ofNat,Nat.cast_mul]; omega
   exact ⟨fun z=> (h z).1,fun z=> (h z).2⟩
 have ht : separation A (R.parent v) ≤ 3:=by
    have h:= Corona.foreshorten R (R.embed A) v; rw [Ratio.embed_parent] at h; refine Nat.le_of_mul_le_mul_left (le_trans h ?_) R.count.property; exact le_trans (Nat.add_le_add_right hh _) (le_of_eq (by unfold R ratio; ring))
 have hg:separation A B ≤2*separation x y:=by
    unfold A B node; rw [separation_translate]; unfold separation; let C:= assembly c; change pdist (C.embed x-C.embed y)≤ _; rw [← Ratio.root_embed,← Ratio.root_embed,←map_sub, Ratio.root_embed]; apply Finset.sup_le; intro i _; change (lift _ i).natAbs ≤ _; rw [Ratio.lift_embed,Pi.smul_apply,nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left 2 (component_le (x-y) i)
 change separation (R.parent v) B≤_; exact ((separation_triangle ..).trans (add_le_add ((separation_comm ..).trans_le ht) hg)).trans (by omega)
def arch(G:Ratio c f)(P:Op (Iota G)): Matrix (Single f) (Single c) ℂ:=Matrix.of fun x y=> P ((switchG G).symm x) (patchQ G y)
structure BudH (G:Ratio c f)(K:Matrix (Single f) (Single c) ℂ)(a V:ℝ):Prop where
 stem(x):∑ i,bolt a G x i * ‖K x i‖ ≤ V*followV [] G.count
 hip(y):∑ x, bolt a G x y*‖K x y‖ ≤ V*((G.count.val:ℝ)^4*followV [] G.count)
private lemma stamp_h(x y:Site c): separation x (x+y)= pdist y:=by rw [separation_comm,separation,add_sub_cancel_left]
lemma plate_e{k:Type*}[Fintype k][DecidableEq k]{P:Cover→Op k}{a b:k}{η C:ℝ}(h:0<η)(p:Width η C fun v=> P v a b)(x:Site c): ∑ y: Site c,Faro η x y*‖cart c P (x,a) (y,b)‖ ≤ C:=by
 let g:=fun z=>Rush.wind x z* P z a b; have he(i): ‖g i‖=‖P i a b‖:=by unfold g; rw [norm_mul,Rush.wind,fee_norm,one_mul]
 apply le_trans (le_of_eq ?_) (tinct x (g:=g) h.le (by simpa only [Width,he] using p)) -- tune
 simp only [cart,Matrix.of_apply,wagon_app]; simp only [g,eq_comm]
lemma fiz (N:Side)(x y k: Site N):frequency k (x+y)=frequency k x*frequency k y*Rush.wind x (natural y):=by
 have hh:=freq_advance k x (natural y); rw [freq_mode,nat_true] at hh; rw [← hh,mul_comm _ (Rush.wind _ _),←mul_assoc, Rush.wind,fee_one,one_mul]
lemma waggle {k:Type*}[Fintype k][DecidableEq k](x y z:Site c)(b i:k){P:Cover→Op k}{V:Momentum→Op k}(p:Reads P V): ‖cart c P (x,b) (y,i)‖= ‖cart c P (x+z,b) (y+z,i)‖:=by
 let Z:= Rush.wind x (natural z); let Y:=Rush.wind y (natural z)
 have hp : cart c P (x+z,b) (y+z,i)= Z*Y*cart c P (x,b) (y,i):=by
   rw [cart_traded p,Rush.price,Rush.price, Finset.mul_sum]; refine sum_congr rfl fun a _=>?_
   simp only [Fourier,Matrix.of_apply,fiz]; unfold Z Y; generalize H: frequency a z=t
   have hv:star t * t=1:=H ▸ frequency_unit a z; simp only [star_mul, star_div₀,Rush.wind,fee_real]; -- tune
   symm; calc
     _ = _ * (star t * t) := (by rw [hv,mul_one])
     _ = _:=by ring
 rw [hp,norm_mul,norm_mul,show ‖Z‖=1 from fee_norm _,show ‖Y‖=1 from fee_norm _,one_mul,one_mul]
lemma plate_f{k:Type*}[Fintype k][DecidableEq k]{P:Cover→Op k}{a b:k}{η C:ℝ}{V:Momentum→Op k}(H: Reads P V)(h:0<η)(p:Width η C fun v=> P v a b)(x:Site c): ∑ y: Site c,Faro η y x*‖cart c P (y,a) (x,b)‖ ≤ C:=by
 refine le_trans (le_of_eq ?_) (plate_e h p x); let E:Equiv.Perm (Site c):= (Equiv.neg _).trans (Equiv.addRight (x+x)); conv_rhs => rw [← Equiv.sum_comp E]
 apply sum_congr rfl; intro y _; let t:= x-y; have hx:y+t=x:=by unfold t; abel
 rw [waggle y x t a b H,hx, show E y=x+t by change -y+(x+x)= x+t; unfold t; abel]
 unfold Faro; have hh:= separation_translate y x t; rw [hx] at hh; rw [hh]
end YM.CF.Font
