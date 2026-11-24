import YM.CF.Dial.Press
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def bookK(x:Bale N P)(y:Bale N P)(S: Seal (Site (More P))):ℝ:=deal G S x.1 y.1+(∑ i∈ S, ‖x.2.1 i-y.2.1 i‖)+(∑ i∈cloudG G S, ‖x.2.2 i-y.2.2 i‖)
lemma bk(x y S):0≤bookK G x y S:= add_nonneg (add_nonneg (deal_pos ..) (by positivity)) (by positivity)
lemma cloud_grows{S T}(h:S⊆T):cloudG G S⊆cloudG G T:=fun i hi=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hi).2⟩
lemma bk_m (x y) : Monotone (bookK G x y) := fun _ _ h=> add_le_add (add_le_add (deal_le G h x.1 y.1) (Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _=>norm_nonneg _))) (sum_le_sum_of_subset_of_nonneg (cloud_grows G h) (fun _ _ _=>norm_nonneg _))
abbrev TopK (e:ℝ):= ↥(zoneP G e)
def curveD(e:ℝ): Stage (Site (More P)) (Iota G) (TopK G e) (Site (More P)→E):=⟨terr _,(tempo G 1).home,fun g x=> ⟨novel G g x.val,cyl G g x.val x.property⟩, fun S x y=>bookK G x y S /|e|, fun S x y=>div_nonneg (bk ..) (abs_nonneg _),fun p x y=>div_le_div_of_nonneg_right (bk_m G _ _ p) (abs_nonneg _)⟩
-- far right endpoints have conjugate color data
abbrev AxisT := Bool × Bool
def rod (u:Bool)(e:ℝ): Branch.Tag (curveD G e):=⟨(Peaks.parcel G u e).run, (Peaks.parcel G u e).keeps⟩
def rope (u:AxisT)(e:ℝ): Branch.Tag (curveD G e):= if u.2 then rod G u.1 e else (rod G u.1 e).reverseV
lemma cD(e:ℝ): Capacity (curveD G e) quota := ⟨glen,(temper_cap G 1).ball, (temper_cap G 1).place⟩

-- slow transports
omit G
lemma stroll_h (U:Bkg N)(X:Site N→Vect)(p:ℝ)(h:Slow U X p)(l:Walk)(x:Site N): ‖turn (travel U x l) (X (stop x l))-X x‖ ≤ l.length*p :=by
  induction l generalizing x with
  | nil=> simp [travel,stop,turn,fund_one]
  | cons i l ih=>
    let y : Site N:= x+i.vec
    have he: ‖turn (i.read U x) (X y)-X x‖≤ p:=by
      rcases i with ⟨i,f|f⟩
      · exact (h _ _).le -- Bool
      change ‖turn (_⁻¹) (X (x+ -step i))-X x‖ ≤ p
      let S:=x-step i; let Q:=U (S,i);
      have he:= h S i; rw [show S+step i=x from sub_add_cancel ..] at he
      rw [show x + -step i=S from (sub_eq_add_neg ..).symm]; change ‖turn Q⁻¹ _-_‖≤_
      rw [← turn_norm Q,turn_sub, ← turn_seq,mul_inv_cancel,show ∀ x:Vect,turn 1 x=x by intro; simp [turn,fund_one],norm_sub_rev]; exact he.le
    rw [travel,stop,turn_seq]; apply (norm_sub_le_norm_sub_add_norm_sub _ (turn (i.read U x) (X y)) _).trans
    rw [←turn_sub,turn_norm,List.length_cons]; push_cast; rw [add_mul,one_mul]; exact add_le_add (ih y) he
include G
def hueK (g:E)(o:Site (More P))(U:Sew N P)(x:Site (More P)):E:=g⁻¹ * hue U.1.1 o x
lemma hear (g:E)(o:Site (More P))(U:Sew N P)(he:U.2.1 o=scaledV g apex)(x:Sew N P)(hx:frost G (hueK g o U) U=x)(e:ℝ)(p:0<e)(hp:Gild G U e)(m:ℕ):
 let S:=bay (terr _) o m
 (∀ i∈S, ‖hook x.2.1 i-apex.val‖ ≤ (4*m:ℕ)*e) ∧ ∀ i∈cloudG G S, ‖hook x.2.2 i-apex.val‖ ≤ (4*m:ℕ)*e +e:=by
  subst x; let y:=frost G (hueK g o U) U
  intro S; have hx(i)(hz:i∈ S): ‖hook y.2.1 i-apex.val‖ ≤ ((4*m:ℕ):ℝ)*e:=by
    let C:=hue U.1.1 o i
    let Z:=U.2.1 i
    have hg:=stroll_h _ _ _ hp.loS (Cube.march o i 1) o; rw [Cube.arrive] at hg
    change ‖turn (g⁻¹ * C) Z.val-apex.val‖ ≤ _
    rw [turn_seq,← turn_norm g,turn_sub,←turn_seq,mul_inv_cancel,turn,fund_one,act_one]
    rw [show turn g _= (U.2.1 o).val from congr_arg Subtype.val he.symm]
    apply hg.trans; apply mul_le_mul_of_nonneg_right _ p.le
    have hh : (Cube.march o i 1).length ≤4*m:=by apply Cube.march_len _ _ _; rw [separation_comm]; exact (bay_mem _).mp hz
    exact_mod_cast hh
  refine ⟨hx,fun i hu=>?_⟩; apply (norm_sub_le_norm_sub_add_norm_sub _ (hook y.2.1 ((ratio G).embed i)) _).trans; rw [add_comm _ e,norm_sub_rev (hook _ _)]
  exact add_le_add ((solid G (hueK g o U) hp).pegS i).le (hx _ (mem_filter.mp hu).2)
-- price for gauge part
lemma prism_g (U:Sew N P)(g:E)(o:Site (More P))(m:ℕ)(e:ℝ)(h:Gild G U e)(p:0<e)(hw:2*(m+G.count.val)+2<(More P).val) :
 let x:=frost G (hueK g o U) U; let S:=bay (terr _) o m; let V:=priceF (m+G.count.val) e;
 (∀ i∈ leaks S, ‖brand (x.1.1 i)-1‖ ≤ V)∧∀ i∈leaks (cloudG G S),‖brand (x.1.2 i)-1‖≤e+G.count.val*V:=by
  intro x S V
  let X:=july G (hue U.1.1 o) U.1; obtain ⟨hv,hQ⟩:= compNear G p.le U.1 h.covW m o hw
  have hc(a b c y:E)(l:E): ‖brand ((g⁻¹*a)*y*(g⁻¹*b)⁻¹)-1‖=‖brand (a*y*b⁻¹)-1‖:=by
    have he : (g⁻¹*a)*y*(g⁻¹*b)⁻¹=g⁻¹*(a*y*b⁻¹)*g:=by group
    rw [he,brand_mul,brand_mul,show brand g=star (brand g⁻¹) by rw [brand_inv,star_star]]
    let K:=brand g⁻¹; have hh:K*star K=1 := (brand_unit g⁻¹).2
    change ‖K*_*star K-1‖=_; rw [show K*brand (a*y*b⁻¹)*star K-1= K*(brand (a*y*b⁻¹)-1)*star K by rw [mul_sub,mul_one,sub_mul,hh]]; rw [brand_rig,brand_lef]
  exact ⟨fun i hg=>(hc _ _ g _ g).le.trans (hv i hg),fun i hg=>(hc _ _ g _ g).le.trans (hQ i hg)⟩ -- implicit mismatch
end YM.CF.Dial
