import YM.CF.Skye.Knit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m:Side}{u d e a:ℝ}{r:ℕ}(q:Chi)
-- clipping chord to replica through forest
lemma narrowX (a:ℝ)(t:0<a):∃ d:ℝ,0<d ∧2*d< firstRadius group∧∀ q:Chi,∀ x y:E, ‖brand (knit q d x y)-brand y‖≤ a:=by
 let f:= brand ∘ group.lieExp
 have h:Continuous f:= Dial.spinD.comp group.lieExp_cont -- tune
 have ht: Tendsto f (𝓝 0) (𝓝 1):=by have ht:= h.tendsto 0; rw [show f 0=1 by simp [f, brand_one]] at ht; exact ht
 obtain ⟨k,he,hP⟩:=Metric.mem_nhds_iff.mp (ht.eventually (ball_mem_nhds 1 t))
 let d:= min k (firstRadius group); have hp:0<d:=lt_min he (first_pos _)
 refine ⟨d/3,by positivity,by linarith [show d≤firstRadius group from min_le_right ..],fun q x y=>?_⟩
 let z:=patched q (d/3) (x*y⁻¹); rw [knit, brand_mul,show _*brand y-brand y=(f z-1)*star (brand y⁻¹) by rw [brand_inv,star_star, sub_mul,one_mul]; rfl,brand_rig]; exact (mem_ball_iff_norm.mp (show f z∈ball _ a from hP (show z ∈ ball 0 k from mem_ball_iff_norm.mpr (by rw [sub_zero]; apply lt_of_le_of_lt (patched_small q (by positivity) _); linarith [show d≤k from min_le_left ..])))).le -- tune
lemma bumps (W Z:Pane n)(k:∀ i,‖brand (W i)-brand (Z i)‖≤a)(x:Seat n)(l:Walk): ‖brand (travel W x l)-brand (travel Z x l)‖≤ l.length*a:=by
 induction l generalizing x with
 | nil=> simp [travel]
 | cons i l ih=>
    let w:= brand (i.read W x); let z:=brand (i.read Z x); let v:=brand (travel W (x+i.vec) l); let t:=brand (travel Z (x+i.vec) l)
    have he:‖w-z‖≤a:=by unfold w z; rcases i with ⟨i,h|h⟩; exact k (x,i); change ‖brand _⁻¹-brand _⁻¹‖≤ _; rw [ticket_inv]; exact k _
    rw [travel,travel,brand_mul,brand_mul,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; change ‖w*v-z*t‖≤ _
    refine (norm_sub_le_norm_sub_add_norm_sub _ (w*t) _).trans ((add_le_add ?_ ?_).trans le_rfl)
    · rw [←mul_sub,show ‖w*_‖=_ from brand_lef ..]; exact ih _
    rw [←sub_mul,show ‖(w-z)*t‖=‖w-z‖ from by unfold t; rw [show brand (travel Z _ _)=star (brand (travel Z (x+i.vec) l)⁻¹) by rw [brand_inv,star_star]]; exact brand_rig _ _]; exact he -- tune
lemma turns_B (W Z:Pane n)(p: Guard Z u)(k:∀ i,‖brand (W i)-brand (Z i)‖≤a): Guard W (u+4*a):=by
 have hp (b:Seat n)(i j:Axis)(g:i≠j):let w(x:Pane n):=brand (travel x b (square i j)); ‖w W-1‖≤u+4*a:=by
    intro w; have ht:‖w Z-1‖≤u:=by rw [Prod.norm_def]; exact max_le (p.2 b i j g) (p.1 b i j g)
    refine (norm_sub_le_norm_sub_add_norm_sub (w W) (w Z) _).trans ((add_le_add (b:=4*a) ?_ ht).trans (le_of_eq (add_comm ..))); exact bumps _ _ k b _ -- tune
 exact ⟨fun x i j g=>(norm_snd_le _).trans (hp x i j g),fun x i j g=>(norm_fst_le _).trans (hp x i j g)⟩
variable (G:Ratio n m)(F:Forest (ratio G))(V:Pane n)(W:Pane m)
def portU (q:Chi)(d:ℝ)(W:Pane m)(V: Pane n): Pane m:=fun i=> knit q d (gauge (F.foldAt W) W i) (Precision.replica (ratio G) V i)
def seine (q:Chi)(d:ℝ)(W:Pane m)(V: Pane n): Pane m:= Lattice.gauge (F.foldAt W)⁻¹ (portU G F q d W V)
lemma cycleY (o:Odd G.count.val)(p:Guard V u)(hx:0≤u)(k:8<(More n).val)(hf: 2*G.count.val < (More n).val)(ht:64*u+4*a≤ e)(hp:G.count.val*a≤e)(hv:u≤e)(hq:∀ x y:E,‖brand (knit q d x y)-brand y‖≤a):JointB G (seine G F q d W V,V) e:=by
 let Z:=portU G F q d W V; let Y:= Precision.replica (ratio G) V; have he(i):‖brand (Z i)-brand (Y i)‖≤a:=hq ..
 have hV:JointB G (Z,V) e:=by
   refine ⟨((turns_B _ Y (wingJ G o V p hx k) he).shrink ht),p.shrink hv,fun i=>?_⟩
   have hx:= bumps Z Y he ((ratio G).embed i.1) (pathL G i.2); rw [show travel Y _ _=_ from newt G o V i hf, norm_sub_rev,pathGL] at hx; exact hx.trans hp
 have hh(X:Seat n): (F.foldAt W)⁻¹ ((ratio G).embed X)=1:=by rw [Pi.inv_apply,F.fold_root,inv_one]
 rw [show (seine G F q d W V,V) = july G (F.foldAt W)⁻¹ (Z,V) from ?_]; exact joint_g G _ hV _
 refine Prod.ext rfl ?_; change V=Lattice.gauge (scaleG G _) _; funext i; simp [Lattice.gauge,scaleG,hh,F.fold_root]
theorem smock(L:Side)(e:ℝ)(p:0<e):∃ u d:ℝ,0<u∧u≤e∧0<d∧ 2*d< firstRadius group∧∀ {n m:Side}(G:Ratio n m)(F:Forest (ratio G)), Odd G.count.val→G.count=L→max 8 (2*L.val)<(More n).val→∀ (q:Chi)(W:Pane m)(V:Pane n),Guard V u→JointB G (seine G F q d W V,V) e:=by
 let u:= e/128; let a:=u/(L.val:ℝ); have hu:0<u:=(by positivity); have ht:0<a:=(by positivity); obtain ⟨b,h,k,H⟩:=narrowX a ht
 refine ⟨u,b,hu,by unfold u; linarith,h,k,fun G F hx hs hg q W V t=>cycleY q G F V W hx t hu.le ((le_max_left ..).trans_lt hg) (hs.symm ▸ (le_max_right ..|>.trans_lt hg)) ?_ ?_ ?_ (H q)⟩
 all_goals have hy:1≤ (L.val:ℝ):=by exact_mod_cast (L.property : 1≤ L.val)
 · have hf:a≤u:= div_le_self hu.le hy; unfold u at *; linarith
 · rw [hs]; unfold a; rw [mul_div_cancel₀ _ (lt_of_lt_of_le one_pos hy).ne']; unfold u; linarith
 unfold u; linarith
end YM.CF.Skye
