import YM.CF.BPress.Lilac.Reveal
/-! count fixed-window witnesses. even $L_c$. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger
variable {N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {X: Sugar.Stage N}{Y:Driver N}
open Bias Bias.Sails
namespace Born
variable (p:Born A R X Y)(i:BlockY A R)(r n:ℕ)(z:Fin 5)
private def apron(x:Tri N) : Tri (More N):= fun i=> nodeT (x i)
lemma upFace (x:Tri N)(t: Per N):Fin.tail (node (BPress.event t x))=apron x:= funext fun i=> node_κ (BPress.event t x) i.succ
def bumpa (x:Patio R): Tri (More N):= (porch A R i x).2
lemma clockA (C: Side)(g:R.L.val=C.val+C.val) (v:Fin 3→Fin C.val): ∃ x:Tri N, tang R (apron x)=i.2 ∧ ∀ j,(packB R (apron x) j).val=2*(v j).val+1:=by
 let s:=More N; let J:= Fin 3; let K(j):= v j; have he(j:J):2*(K j).val+1<R.L.val:=by have he:=(K j).isLt; omega
 let L:Patio R:= fun j=>⟨_,he j⟩; let W:=bumpa i L; suffices ∃ x:Tri N,apron x=W by obtain ⟨x,h⟩:=this; refine ⟨x,(by rw [h]; exact congrArg Prod.snd (porch_own ..)),fun j=>?_⟩; rw [h]; exact congrArg Fin.val (congrFun (pack_p A R i L) j)
 let U(j):ℕ:= C.val * (i.2 j).val + (v j).val; have ht(j): (W j).val=2*U j+1:=by
    have he: (W j).val = R.L.val*(i.2 j).val+(2*(v j).val+1):= by have u:= Radix.dial_val (More N) R.L R.period R.geom (0:Per s) (i.2 j) _ (L j).isLt; rw [sub_zero] at u; exact u
    rw [he,g]; unfold U; ring
 have hn(j): U j<N.val:=by have hp:=(ht j).symm.trans_lt ((W j).val_lt); have hh:(More N).val = N.val*2:=rfl; omega
 refine ⟨fun j=> (↑(U j):Per N),funext (fun j=> ZMod.val_injective _ (?_))⟩; rw [apron,nodeT_v,ht,ZMod.val_natCast_of_lt (hn j)]
lemma packed (e:Even R.L.val): ∃ (C:Side)(g: (Fin 3 → Fin C.val)→ Tri N), R.L.val=C.val+C.val∧ Injective g ∧ ∀ v,tang R (apron (g v))=i.2:=by
 obtain ⟨a,p⟩:=e; have x:R.L.val=a+a:=p; have hp:0<a:= by apply Nat.pos_of_ne_zero; intro j; have he: R.L.val≠0:= R.L.property.ne'; apply he; rw [x,j]
 let C:Side:= ⟨a,hp⟩; choose g h u using fun v=> clockA i C x v; refine ⟨C,g,x,fun a b v=> ?_,h⟩; funext j; apply Fin.ext; have h₁:=u a j; have h₂:=u b j; rw [v] at h₁; omega
variable {r n z}
lemma ledgers {c:ℝ}(h:ShineZ p r c z)(g:r≤n) (v:n ≤ Wealth.cloak B) (e:Even R.L.val) : (∑ a∈positions A R i n,p.BiasQ z a) ≤ -(c/8)* (R.L.val:ℝ)^3:=by
 obtain ⟨C,G,X₀,T,D⟩:= packed i e; let V:= Fin 3→ Fin C.val; choose t ht H using fun a:V=> h.star i.1 (G a); let f(x:V):= node (BPress.event (t x) (G x)); let S:= positions A R i n; have he(x:V): f x∈S:=by
    let a:i.1=i.1:=rfl; have hp': f x∈ reachP (A:=A) i.1 n:=by
       apply (zone_of_halo ..).2; obtain ⟨b,e,d⟩:= (mem_filter.mp (ht x)).2; refine ⟨b,e,?_ ⟩; unfold f; rw [node_κ]; exact d.trans g
    refine mem_filter.mpr ⟨mem_univ _,Prod.ext (moment_p A v hp') ?_, near_gap hp'⟩; change tang R (Fin.tail (node (BPress.event (t x) (G x))))=i.2; rw [upFace]; exact D _
 have hi : Injective f:=by intro x y e; apply T; simpa [BPress.event] using congrArg (fun a:Site N=>Fin.tail a) (Tenant.needle e)
 let Q:=univ.image f; have hp: Q ⊆ S:=by intro i t; obtain ⟨i,v,rfl⟩:= mem_image.mp t; exact he i
 have ht:= sum_le_sum_of_subset_of_nonneg hp (fun i _ _=> show 0≤ -(p.BiasQ z i) from neg_nonneg.mpr (p.posting z i)); simp only [sum_neg_distrib,neg_le_neg_iff] at ht; apply ht.trans
 unfold Q; rw [sum_image (g:=f) (fun i _ j _ t=> hi t)]; apply le_trans (sum_le_sum (g:=fun _=> -c) (?_)) (?_); · exact fun _ _=> H _
 rw [sum_const,nsmul_eq_mul,card_univ]; simp only [V,Fintype.card_pi_const,Fintype.card_fin, X₀, Nat.cast_add, Nat.cast_pow]; exact Eq.le (by ring)
-- purchase universal c,n,r
end Born
end YM.CF.BPress.Lilac
