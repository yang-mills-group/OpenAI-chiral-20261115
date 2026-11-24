import YM.CF.Mesa.Belt
import YM.Branch.Pick

/-! From small curvature in full cubes to the protection test. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
abbrev lambda := SU.group.chord
variable {m B:Side}
def weakPin (a:Index m)(U:Bkg (Domain m B))(e:ℝ):=∀ x:Site (Domain m B),separation x (address m B a)≤B.val →∀ i:PlaqAxes,lambda (faceValue U (x,i))≤ e
private lemma deltaS (u v:SU.E): GDist u v=lambda (u*v⁻¹)*(Real.sqrt (SU.group.repDim:ℝ)):=by
  unfold GDist lambda Gauge.chord; rw [div_mul_cancel₀,← bolt u v v⁻¹,dist_eq_norm,mul_inv_cancel]; rfl
  exact (Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)).ne'
private lemma target (B:Side):∃ r:ℝ, 0<r∧∀ U:Links ℤ SU.E,(∀ x∈box B.val, ∀ i:PlaqAxes,lambda (faceValue U (x,i))≤r) →∃ h:Cover→SU.E,∀(x) (i), x∈box B.val→x+step i∈box B.val→ GDist (h x*U (x,i)) (h (x+step i)) ≤ 1/(B.val:ℝ):=by
  let X:=box B.val
  let l:=allAxes 1; have ht:l.Nodup:=(List.nodup_finRange _).map (show Lattice.Order from 1).injective
  have he : Lattice.slab B.val 0 l=X :=by
    ext i
    simp only [slab_iff]
    have ha (j:Axis) : j ∈ l:=by simp [l,allAxes]
    simp [ha,X]
  let t:ℝ:=(Finset.univ:Finset PlaqAxes).card; let N:ℝ:=4*(l.length:ℝ)*(layers B.val).card
  let w:ℝ:=Real.sqrt (SU.group.repDim:ℝ)
  have hn : 0≤N:=by unfold N; positivity
  have hT:0≤t:=by unfold t; positivity
  have hw:0≤ w:=by unfold w; positivity
  let J:ℝ:=N*X.card*t*w; have hJ:0≤J:=by unfold J; positivity
  let k:ℝ:= 1/(B.val:ℝ); let r:=k/(J+1); have hp:0<r:=by unfold r k; positivity
  refine ⟨r,hp,fun U g=>?_⟩
  have hm:= Axial.existence l B.val 0 U ht (center_box _); rw [he] at hm
  obtain ⟨i,-,hx⟩:= hm
  let H:=Axial.traveller l U i; let V:=gauge H U
  have hr: Axial.faces X U ≤ (X.card:ℝ)*(t*r) := by
    unfold Axial.faces
    refine (Finset.sum_le_sum (g:=fun _=>t*r) (fun i hi=>?_)).trans (le_of_eq (by simp))
    refine (Finset.sum_le_sum (g:=fun x:PlaqAxes=>r) (fun x _=>show Axial.face X U i x≤ r from ?_)).trans (le_of_eq (by simp [t]))
    unfold Axial.face; split; exact g i hi x; exact hp.le
  have hL: ∀ x i, 0≤ Axial.perEdge X V x i:=fun x j=> by unfold Axial.perEdge; split; exact SU.group.chord_nonneg _; rfl
  refine ⟨H,fun x j u h=>?_⟩
  have hA :lambda (V (x,j))≤ Axial.edges X V :=by
    rw [show lambda _=Axial.perEdge X V x j from (if_pos h).symm]
    exact le_trans (Finset.single_le_sum (f:=Axial.perEdge X V x) (fun i _=>hL x i) (Finset.mem_univ j)) (Finset.single_le_sum (fun i _=> Finset.sum_nonneg (fun k _=>hL i k)) u)
  have hb:r*(J+1)=k:=by unfold r; field_simp
  rw [deltaS]; apply (mul_le_mul_of_nonneg_right (hA.trans (hx.trans (mul_le_mul_of_nonneg_left hr hn))) hw).trans
  change N*_*w ≤ k
  unfold J at hb; nlinarith only [hb,hp]
lemma booth (B:Side):∃ e:ℝ,0<e∧∀ m (a:Index m), 2≤m.val→∀ U:Bkg (Domain m B), weakPin a U e→∃ h: Fa m B,Bed a 1 U h:=by
  obtain ⟨r,hp,H⟩:= target B; refine ⟨r,hp,fun m a h U g=>?_⟩
  let Y:=Domain m B; let x:=address m B a; let W:= expandAt x U
  have hb y (s:y∈box B.val) : ∀ i, ((y:Cover) i).natAbs ≤ B.val := fun i=>by obtain ⟨g,h⟩:=box_test.mp s; have h₁:=g i; have h₂:=h i; omega
  obtain ⟨k,hk⟩:= H W (fun y s i=>by
    let z:=wrap Y y+x
    rw [faceValue,show W=expandAt x U from rfl,travel_at]
    apply g z _ _; unfold separation pdist; refine Finset.sup_le ?_; intro j _; change ((lift (z-x)) j).natAbs≤_;rw [show z-x=wrap Y y by unfold z; abel,lift_s (fun t=>le_trans (hb y s t) (by omega)) h]; exact hb y s j)
  have he (v) (hv:v∈room m B a):offs a v∈box B.val:= by
    rw [box_test]; constructor <;> intro j <;> have H:=(off_cap hv j).trans (broad_le ..) <;> omega
  refine ⟨k ∘ offs a,fun ⟨z,j⟩ ⟨q,t⟩=>?_⟩
  have hv:offs a (z+step j)=offs a z+step j:= by
    have hZ:= off_lift t q h; change lift (z+step j-z)=_ at hZ; rw [add_comm z,add_sub_cancel_right,lift_step] at hZ; rw [hZ]; abel
    have hi:=wide m B h; have ht:0<B.val:=B.property; omega
  have hY:W (offs a z,j)=U (z,j) := by
    have hx :=off_back a z; change U (wrap Y (offs a z)+x,j)=_
    rw [add_comm,show x+wrap Y (offs a z)=z from hx.symm]
  have hh:=hk (offs a z) j (he z q) (hv ▸ he _ t); rw [←hv,hY] at hh; exact hh
end YM.CF.Mesa
