import YM.CF.Brace.Fish
/-! Pairing transfer, coarse values lifted on refined gauge sites via exact local routes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
abbrev Fend (N:Side):= Site (More N)
def dart (o:Fend P): Walk:=march o ((ratio G).embed ((ratio G).parent o)) 1
def ascend (x:Stun N)(U: Bkg (More P)): Stun P:= fun i=> scaledV (travel U i (dart G i)) (x ((ratio G).parent i))
lemma adel(x:Stun N)(U:Bkg (More P))(i:Fend N): ascend G x U ((ratio G).embed i)=x i:=by
 apply Subtype.ext; have he(g:Ratio N P): ∀ i, (ratio g).parent ((ratio g).embed i)=i:= by
   intro i; let R:=ratio g; change R.parent _=_; have he:R.embed i=R.assemble (i,0):= by simp [Ratio.assemble]
   rw [he,Ratio.assemble_parent]
 rw [ascend,dart,he]; change turn _ (x i).val=_; unfold march; rw [sub_self]; rw [show lift (0:Site (More P))=0 from by simp, route_same,travel,turn,fund_one,act_one]
lemma ascent_c :Continuous (fun x:Stun N × Bkg (More P)=> ascend G x.1 x.2):= by
 apply continuous_pi; intro i; let f:= fun x: Stun N× Bkg (More P)=> travel x.2 i (dart G i); let J:= fun x: Stun N× Bkg (More P)=> x.1 ((ratio G).parent i)
 have he : Continuous f:= (travel_cont (K:=E) i (dart G i)).comp continuous_snd; have ht: Continuous J:= (show Continuous (fun x:Stun N=> x ((ratio G).parent i)) from continuous_apply _).comp continuous_fst
 change Continuous ((fun x:E × Ballot=>scaledV x.1 x.2) ∘ (fun x=>(f x,J x))); exact scaled_cont.comp (he.prodMk ht) -- tune
lemma ascent_g (U:Bkg (More P))(g:Fend P→ E)(x):ascend G (feast (scaleG G g) x) (gauge g U)=feast g (ascend G x U):=by
 funext i; apply Subtype.ext; rw [ascend,travel_gauge, show stop i (dart G i) = _ from (Cube.arrive i ((ratio G).embed ((ratio G).parent i)) 1)]; unfold feast ascend scaledV scaleG; simp only [comp_apply]; rw [turn_seq,turn_inv_g,turn_seq]

lemma parentsN (G:Ratio N P)(x:Site P): separation x (G.embed (G.parent x))≤ G.count.val:=by
 rw [separation]; apply Finset.sup_le; intro i _; have he:x-G.embed (G.parent x)= wrap P (lift (G.residue x)):= by
   rw [sub_eq_iff_eq_add,add_comm]; exact (G.unpack_at x).symm
 have hz:=lift_centers (G.residue x); rw [he]; have hf:lift (wrap P (lift (G.residue x)))=lift (G.residue x):=by
   rw [lift_eq_iff]; refine ⟨rfl,fun j=>?_⟩; obtain ⟨h,p⟩:=hz j; have he:G.count.val≤P.val:=by rw [G.exact_size, mul_comm]; exact Nat.le_mul_of_pos_right _ N.property; -- tune
   omega
 rw [hf]; have hx:=hz i; omega
lemma parentsK (G:Ratio N P)(x:Site P)(j:Axis): separation (G.parent x) (G.parent (x+step j))≤ 2*G.count.val+1 :=by
 let y:=x+step j; let u:=G.parent x; let v:=G.parent y; let d:=G.count.val
 have ht: separation (G.embed u) (G.embed v)≤2*d+1:=by
   have hx:separation (G.embed u) x≤d:=by rw [separation_comm]; exact parentsN G x
   have hy :separation y (G.embed v)≤d:= parentsN G y; have hp:separation x y≤1:=oneTouch x j
   apply (separation_triangle (G.embed u) x (G.embed v)).trans; apply (_root_.le_trans (Nat.add_le_add hx ( (separation_triangle x y _).trans (Nat.add_le_add hp hy)))); omega
 change (separation u v)≤_
 unfold separation; apply Finset.sup_le; intro i _
 have he := (component_le (G.embed u-G.embed v) i).trans ht
 rw [←Ratio.root_embed, ← Ratio.root_embed,←map_sub,Ratio.root_embed,Ratio.lift_embed] at he
 simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast] at he; change _≤_; exact (Nat.le_mul_of_pos_left _ G.count.property).trans he
lemma dartK(x:Fend P): (dart G x).length ≤4*G.count.val:=by apply march_len; rw [separation_comm]; exact parentsN (ratio G) x

def leapK(j:Step):Walk:=List.replicate G.count.val j
def sail (l:Walk): Walk:= l.flatMap (leapK G)
lemma walk_len(l:Walk): (sail G l).length=G.count.val*l.length:=by induction l with | nil=>simp [sail]| cons i l ih=> rw [show sail G (i::l)=leapK G i++sail G l from rfl, List.length_append, ih]; simp [leapK,mul_add,add_comm]
lemma stop_s(x:Fend N)(d:Step): stop ((ratio G).embed x) (leapK G d)= (ratio G).embed (x+d.vec):=by
 let R:=ratio G
 have h (n:ℕ)(x:Fend P): stop x (List.replicate n d)= x+n • d.vec:=by induction n generalizing x with| zero=>simp [stop]| succ n ih=> rw [List.replicate_succ,stop,ih,add_smul,one_smul]; abel
 rw [leapK,h]; change _= (ratio G).embed _; rcases d with ⟨i,t|t⟩; exact (mapsG ..).symm
 have he:=mapsG G (x+ -step i) i; rw [show x+ -step i+step i=x by abel] at he; change _+G.count.val • (-step _)=_; rw [he]; simp; rfl
lemma ratio_cmp (x:Fend N)(d:Step)(U: Nom N P)(e:ℝ)(h:JointB G U e): Cube.cmp firstF (travel U.1 ((ratio G).embed x) (leapK G d)) (d.read U.2 x) ≤ e:=by
  have he (x:Fend N)(i:Axis): Cube.cmp firstF (travel U.1 ((ratio G).embed x) (pathL G i)) (U.2 (x,i))≤ e:=by
    rw [Cube.cmp_sym]; exact (norm_snd_le (brand _-brand _)).trans (h.follow (x,i)) -- explicit
  have ht(i): leapK G (posDir i)=pathL G i := by simp [leapK,pathL,straight,posDir]
  rcases d with ⟨i,t|t⟩; change Cube.cmp _ (travel _ _ (leapK G (posDir i))) _≤_; rw [ht i]; exact he ..
  change Cube.cmp _ (travel _ _ (List.replicate G.count.val (negDir i))) ((U.2 (x-step i,i))⁻¹)≤_
  let l:= pathL G i; have hk:=stopG G (x-step i) i; rw [sub_add_cancel] at hk
  rw [show List.replicate G.count.val (negDir i)= Lattice.reverse l from ?_,←hk]; unfold l; rw [travel_reverse,show ∀ c d:E,Cube.cmp firstF c⁻¹ d⁻¹=Cube.cmp firstF c d from ?_]; exact he _ _
  · intro c d; unfold Cube.cmp; rw [map_inv,map_inv]; change ‖star (firstF c).val-star (firstF d).val‖=_; rw [←star_sub,norm_star]
  rw [show l= leapK G (posDir i) from (ht _).symm]; simp only [Lattice.reverse,leapK,List.reverse_replicate,List.map_replicate]; rfl
end YM.CF.Brace
