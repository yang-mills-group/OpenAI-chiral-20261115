import YM.SU5.Selected.Dais.Rous
/-! control weather for uniform Male on Pane. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel.Rous
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Hill.Box Hill.Post Graph Next.Rank Tree Dais.Parity Py.Rate Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {w j k:ℕ}{M:Jill.Male}{δ δ' γ t τ u v ε θ:ℝ}{n:Side}{r:Side}{A:Orbit n→Pane n}
abbrev timeW (r:Side)(w:ℕ): ℝ:= 4320*(w+1:ℕ)/ (r.val:ℝ)
abbrev mintW (r:Side)(k:ℕ):ℕ:=180*Fintype.card PlaqAxes*4*((k+4)*2+1)^4*r.val^4
lemma coverage (p:Roof n u δ k A) (e:r.val ≤ (More n).val)(v':v≤ u)(S:Orbit n):let X:=modesIn n (iceland r w (A S) v); ((Xᶜ:Finset (Single n)).card:ℝ) ≤ timeW r w*sites n + mintW r k* flakes v S.1:=by
 intro X; let N:=More n; let F:= roughness v S.1; have ht:(Xᶜ:Finset (Single n)).card ≤ ( (12*(N.val / r.val+1)*(w+1)*N.val^3)+(((F.card*4*((k+4)*2+1)^4)* Fintype.card PlaqAxes)* r.val^4))*180 := (fallenB ..).trans (Nat.mul_le_mul_right _ ((countI _).trans (add_le_add (count_edge ..) (Nat.mul_le_mul_right _ (rough_count S p v')))))
 let g:=(N.val:ℝ); have hp: 0<g:= nPos N; let b:=(r.val:ℝ); have he:0<b:= nPos r
 apply (Nat.cast_le.mpr ht).trans; unfold timeW mintW flakes; push_cast; let Q:=(↑(N.val/r.val):ℝ)
 have hx: Q+1 ≤ (2*g)/b:=by rw [le_div_iff₀ he]; calc
    _ ≤ g+b:=by rw [add_mul,one_mul]; exact add_le_add (Nat.cast_mul (α:=ℝ) (N.val/r.val) r.val |>.ge.trans (Nat.cast_le.mpr (Nat.div_mul_le_self ..))) le_rfl -- orientation Eq.ge? Nat.cast_mul -> lhs cast product, want ℝ product ≤g
    _ ≤ _:=by linarith only [show b ≤ g from Nat.cast_le.mpr e]
 let M:=4*((k:ℝ)+4)* 2 -- dummy
 change (12*(Q+1)*(w+1)*g^3+ (((F.card:ℝ)*4*((k+4)*2+1)^4)* _)*b^4)*180≤ 4320*(w+1)/b*g^4+ _ * (F.card:ℝ)
 simp only [div_eq_mul_inv] at hx ⊢; linarith only [mul_le_mul_of_nonneg_right hx (show 0 ≤ ((w:ℝ)+1)*g^3 by positivity)]
private lemma mid_P (w:ℕ)(ε:ℝ)(p:0<ε): ∃ r: Side,timeW r w ≤ ε:=by
 let C:= (4320:ℝ)*(w+1:ℕ); obtain ⟨r,h⟩:= exists_nat_gt (C/ε); let S:Side:=⟨r+1,by omega⟩; have he:C/ε ≤ (S.val:ℝ):= h.le.trans (Nat.cast_le.mpr (Nat.le_succ _)); refine ⟨S,(div_le_iff₀ (nPos _)).mpr (by nlinarith only [(div_le_iff₀ p).mp he])⟩
-- True cone weather. K tick after width chosen. fees `/t²` paid after parameter (independent n)
structure Winters(j:ℕ)(δ:ℝ): Prop where
 bills : ∀ ε:ℝ, 0<ε → ∃ γ:ℝ,0<γ∧∃ w N0:ℕ,∀ n:Side,N0 ≤ n.val → Winter j δ n γ w ε
lemma clear_w(j:ℕ)(p:1≤j): ∃ δ:ℝ,0<δ∧ Winters j δ:=by obtain ⟨δ,h,n,k⟩:= winter j p; exact ⟨δ,h,⟨fun t ht=>by obtain ⟨γ,v,w,g⟩:= k t ht; exact ⟨γ,v,w,n,g⟩⟩⟩
open Pressure
lemma persists(k:ℕ)(b:0<δ)(q:0≤δ')(u0:0<u)(p:δ'≤δ)(j:ℕ)(H:Winters j δ)(x:0<t)(v:t≤1)(e:0<ε): ∃ κ:ℝ,0≤κ∧∃ n0:ℕ,∀ᶠ x:ℝ in atTop, ∀ {N:Side}, n0 ≤ N.val → ∀ (A:Orbit N→ Pane N), Roof N u δ' k A→ ∀ (M:Jill.Male), Brace.Sparkle N δ' M j → ∀ S:Orbit N,
 logo t j M (A S) ≤ logo t j M (1:Pane N)+ ε* sites N+ κ* Py.Rate.Pannier.flakes (temp x) S.1:= by
 let d:=ε*t^2/4; have hp:0<d:=by unfold d; positivity
 obtain ⟨γ,h,w,N0,qK⟩:= H.bills (d/180) (by positivity)
 obtain ⟨r,y⟩:= mid_P w d hp
 obtain ⟨τ,hT,z⟩:= craneReady r w h
 let κ:=(t^2)⁻¹ * mintW r k; refine ⟨κ,by unfold κ; positivity,max N0 r.val,?_⟩
 have H': Tendsto temp atTop (𝓝 0):=CF.BPress.npl_temp.drop
 filter_upwards [eventually_gt_atTop (0:ℝ),H'.eventually (ge_mem_nhds u0),H'.eventually (ge_mem_nhds hT)] with a he hh hg N β A d' M V S; let L:=A S; let n:=More N; let t':=columbia r n; let P:= temp a; let F:= (iceland r w L P); let U:= modesIn N F; let C:= Real.log (grip (tickA N) (spar j M (1:Pane N)) t).det.re / 2; let Q:= ((Uᶜ:Finset (Single N)).card:ℝ); let f:= sites N
 have h':0≤f:=zero_le_one.trans (sites_pos N); have hx:= aria_world r x v (ε:=d/180) (by positivity) b (qK N ((le_max_left ..).trans β)) L (d'.paid S) p V (t'.foldAt L) (z _ (BPress.temp_pos he).le hg L) q
 have hz:=coverage (w:=w) d' (r:=r) (((le_max_right ..).trans β).trans (Nat.le_mul_of_pos_right _ two_pos)) hh S; change Q ≤ timeW r w*f+ _ at hz; let g:=Py.Rate.Pannier.flakes P S.1; let hE:= (mintW r k:ℝ); have hQ: Q≤ d*f+hE*g:=le_trans hz (add_le_add_left (mul_le_mul_of_nonneg_right y h') _)
 have hN:(Fintype.card (Single N):ℝ)≤180*f:=by rw [Pic.units_t]; unfold f sites; gcongr; exact_mod_cast (show N.val ≤ n.val from Nat.le_mul_of_pos_right _ two_pos) -- tune
 apply hx.trans; change C+(t^2)⁻¹ /2 *(_ * _ + Q*2) ≤ C+ε*f+ ((t^2)⁻¹ * hE)*g
 let P':=(t^2)⁻¹; have hV:0<P':= by unfold P'; positivity
 have hu:d*P'=ε/4:=by unfold d P'; field_simp
 nlinarith only [mul_le_mul_of_nonneg_right hN (show 0≤ P'*d from mul_nonneg hV.le hp.le), mul_le_mul_of_nonneg_left hQ hV.le,mul_nonneg e.le h',hu, show d*P'*f=(ε/4)*f from congrArg (· * f) hu]
end YM.CF.Pannier.Chancel.Rous
#print axioms YM.CF.Pannier.Chancel.Rous.persists
