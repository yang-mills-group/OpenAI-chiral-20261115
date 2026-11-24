import YM.CF.Peaks.Lintel
/-! Graph tilt compressed to output sites vanishes to first order in the uniform local calculus (no quantitative rate here). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤j)(T:Script Male)(ht:Use j L T)
variable (u:Bool)
def lum (u:Bool): Script Male:= fun i N P G x=>hood G*((1-wh j L ho u i G x)*ticketT T u i G x*pine j L ho T u i G x)*hood G
include hj he ht
lemma cologne {N P: Side}(G:Ratio N P)(hg:G.count=L)(M:Male):lum j L ho T u M G 1=0:=by
  let R:= hood G
  let V:=wh j L ho u M G 1; let S:=ticketT T u M G 1; let H:=pine j L ho T u M G 1; let P':=foal j u M G 1
  have he':Odd G.count.val:=hg.symm ▸ ho
  have hh:R*S*H*R=(plates N (Fir.grow u j G.count M.val))⊗ₖ (1:Op Slot):=by
    let B:=cart N (tub (boards u j G.count M.val)); let D:=plates N (fun p=> peb G.count)
    have hz:= (sock G j M.val u he hj M.property he').2.2.2.2
    have h1:B*D= _ := hz
    unfold R S H; rw [T_flat j L ho hj G hg M u ht]; dsimp only; rw [piles_conj G j u hj he', crystal j L ho hj he T ht G hg M u,dip];
    rw [doodle G true false _ (cBoards j G.count M.val u he hj M.property he').sumK, shoulder,op_kron_mul,op_kron_mul,op_kron_mul,one_mul,one_mul,one_mul];
    rw [mul_assoc ((plates _ _) * (plates _ _)) (cart _ _), hz]; congr 1
    rw [pilesP,pilesP]; apply pilesE; intro p hp hx
    let X:=trident G.count p; rw [←mul_assoc,←mul_assoc, mul_assoc _ (star (trident G.count p)), (pointed G.count p hp.1).1,mul_one]; exact (emeritus u j G.count M.val hj he' M.property hp hx).1
  have hl:R*V=V*R ∧ V*R= (plates N (Fir.grow u j G.count M.val))⊗ₖ (1:Op Slot):=by
    unfold V R; rw [wh_base j L ho he G hg M u, shoulder]; simp only [op_kron_mul,one_mul,pilesP,vine, mul_add, add_mul,tall_peb,peb_tall,zero_add,(grow_c ..).1,(grow_c ..).2]; trivial
  have hd:V*S*H=V:=by -- via vacc
    obtain ⟨h,f,q,s⟩:=illumine j L ho hj he G hg M u ht
    unfold H; rw [crystal j L ho hj he T ht G hg M u];
    unfold V S; unfold lake at h; rw [mul_assoc, q] at h; exact h
  change R*((1-V)*S*H)*R=0; rw [show (1-V)*S*H=S*H-V by rw [sub_mul,one_mul,sub_mul,hd],mul_sub,sub_mul,← mul_assoc,hh,hl.1,mul_assoc, show R*R=R from (hood_proj G).1,hl.2,sub_self] -- R_eq typo
lemma crucial(d:ℝ)(hd:0<d):∃ a:ℝ,0<a∧ ∃ K:ℕ,∃ e:ℝ,0<e ∧ Tax L (lum j L ho T u) false false a d K e:=by
  have ht':= hood_tag (ι:=Male) L ho; obtain ⟨t,-,y⟩:=cup j L ho hj he ht u
  have hp:Save L false false (lum j L ho T u):=(ht'.mul ((((Save.one Male).sub y).mul t).mul (pine_funds j L ho hj he T ht u))).mul ht'
  obtain ⟨c,F,e,k,hg,p,r,H⟩:=hp; obtain ⟨b,w,he',y,-,v,hY⟩:=curve (A:=lum j L ho T u) H k hg p d hd (fun i _ _ G h _=>cologne j L ho hj he T ht u G h i); exact ⟨b,he',v,w,y,hY⟩
end YM.CF.Peaks
