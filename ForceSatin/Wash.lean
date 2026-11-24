import ForceSatin.Journal
import Risa.Snag
import Verses.Billing
-- adapt Poetry,Costume; joint chart pulled from each Born channel
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Lattice Laurent Bloch Lat Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant Cascade
open Papyrus.Granat Thera Dial Verses
open MeasureTheory RG Exterior Precision Gleam Gleam.Luster Gleam.Luster.Risa Gleam.Luster.Almanac Skye Pannier.Chancel
open Wilson Tree BPress.Spin Branch
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Classical
attribute [local instance] opCStarAlgebra

variable {c n:Side}{r:Ratio c (More n)} {z t:ℝ}
-- finitely many cuts even per-configuration G's costing resources
structure Tiling (c n:Side) (r:Lattice.Ratio c (More n)) where
 odd_width : Odd r.count.val
 fit : 2*(r.count.val+1)<(More n).val
 forest : Forest r
variable (T:Tiling c n r)

lemma trivial_hike {G:Gauge} (j:Walk) (x:Site (More n)):travel (1:Config G (More n)) x j=1:=by induction j generalizing x with
 | nil=> rfl
 | cons i L ih=> rw [travel,ih,mul_one]; unfold Step.read; split; exact inv_one; rfl

variable (U: Pane n)(σ:Signed)
namespace Tiling
-- T.rootCut witness choose deterministic
abbrev silhouette (σ:Signed) (U: Pane n) : Pane n:= pull σ⁻¹ 0 U
def arcs :Seat n→ SU.E:= T.forest.foldAt (silhouette σ U) ∘ affine σ 0
def wash : Pane n:= gauge (T.forest.foldAt U) U
include T
lemma wash_fix (V:T.forest.Slice SU.group) : T.wash (T.forest.drape V)= T.forest.drape V:= by
  have he : T.forest.foldAt (T.forest.drape V) = T.forest.foldAt (G:=SU.group) 1:= T.forest.names _ _ (fun i p=> T.forest.on_tree V ⟨i,p⟩)
  unfold wash; rw [he]; funext i; unfold Lattice.gauge Forest.foldAt; rw [trivial_hike,trivial_hike,inv_one,inv_one,mul_one,one_mul]
lemma wash_invar (k:Seat n→ SU.E)(h:∀ i:Site c,k (r.embed i)=1) : T.wash (gauge k U)=T.wash U :=by
 have hp(i): T.forest.foldAt (G:=SU.group) (gauge k U) i=T.forest.foldAt U i*(k i)⁻¹:=by rw [Forest.foldAt,travel_gauge,T.forest.hike_root,h]; simp [Forest.foldAt]
 unfold wash; funext i; unfold Lattice.gauge at hp ⊢; rw [hp, hp]; group
lemma wash_chart (U:Pane n): ∃ W:T.forest.Slice SU.group,T.forest.drape W= T.wash U:=by
 let X:=T.wash U; refine ⟨fun i=> X i.val,?_⟩; funext x; by_cases h:x∈ T.forest.trunks
 · exact (T.forest.on_tree _ ⟨x,h⟩).trans (T.forest.compress U x h).symm
 exact T.forest.off_tree _ ⟨x,h⟩
@[fun_prop] lemma wash_cont : Continuous T.wash := by
  unfold wash; apply continuous_pi; rintro ⟨x,i⟩; unfold Lattice.gauge; fun_prop
omit T
lemma snow_back (U:Pane n)(σ:Signed) : pull σ 0 (silhouette σ U)=U:=by rw [silhouette,pull_pull,inv_mul_cancel]; simp [affine]
include T
lemma sung : gauge (T.arcs U σ) U = pull σ 0 (T.wash (silhouette σ U)):=by unfold wash; rw [Push.Local.pull_gauge,snow_back]; rfl

-- actual Pull qualification. σ not necessarily proper; Gauge acts on Loom output already on unpulled marks.
lemma safe_chord {t:ℝ} (h:0≤t) {d:Lattice.Step}{i:Seat n} (hr:r.parent i∉ broken r t U)(hq:r.parent i=r.parent (i+d.vec)): SU.group.chord (d.read (T.wash U) i) ≤ suitedFee r.count.val t:=by
 let X:= T.wash U; obtain ⟨V,e⟩:= T.wash_chart U; have hv:broken r t (T.wash U)=broken r t U:=by unfold wash broken; rw [malaise_home]
 rw [←e]; rw [←hv,← e] at hr; rcases d with ⟨d,b|b⟩
 · exact purified h hr T.fit ⟨rfl,hq.symm⟩
 change SU.group.chord (T.forest.drape V (i-step d,d))⁻¹ ≤_; rw [SU.group.chord_inv]; apply purified h hr T.fit; refine ⟨(by simpa [sub_eq_add_neg,Step.vec] using hq.symm),by simp⟩
lemma clear_link (p:0≤ t){i:Seat n}(a:Axis)(h:Gleam.Safe r (broken r t (silhouette σ U)) 1 (σ.act i)): SU.group.chord ((gauge (T.arcs U σ) U) (i,a)) ≤ suitedFee r.count.val t := by
  let x:=σ.act i; let y:=(posDir a).rotate σ; let S:=silhouette σ U
  rw [sung]; change SU.group.chord (y.read (T.wash S) (affine σ 0 i)) ≤ _; rw [show affine σ 0 i=x from add_zero x]
  apply safe_chord (T:=T) S p h.1 (Eq.symm (h.2 _ ?_)); rw [Step.vec_rotate,Step.vec_pos,←σ.act_add, separation_signed]; exact step_towards ..

variable {X:Scree.Loom n} {Y:Orbit n} {b u:ℝ}{w m k:ℕ}
set_option linter.unusedSectionVars false in
private lemma closest (ht:t≤ b){i:Seat n}(p:Gleam.Safe r (broken r t (silhouette σ U)) k (σ.act i)): i ∉ RG.flags b U:=by
 let V:=silhouette σ U; let Z:= (σ.act i : Seat n); let A:=r.parent Z
 intro h
 have hv:= Work.H03.flags_send σ (0:Seat n) b V; rw [show pull σ 0 V= U from snow_back ..] at hv
 have h: affine σ (0:Seat n) i∈ RG.flags b V:=hv ▸ mem_image_of_mem _ h
 obtain ⟨F,c,hk⟩:= (RG.flags_spec ..).1 h
 have hu: affine σ (0:Seat n) i=σ.act i:= add_zero _
 rw [hu] at c
 exact Finset.disjoint_left.mp (Gleam.legit p.1) (show Z∈_ from halo_spec.mpr ⟨_,Finset.mem_singleton_self _,le_trans (near_root _ rfl) (Nat.le_add_right ..)⟩) ((RG.flags_spec ..).mpr ⟨F,c,ht.trans_lt hk⟩)
 -- placeholder scope
-- from Thin Costume, use pulled tree but Loom BEFORE every pull. No comparing tags across two YM appointments
lemma gleam_in_sleeve (l:ℕ) (B:Skye.Roof n b u w X)(d:m+w+1 ≤ l)(p:0≤ t)(e:t ≤ b) (Y:Orbit n)(i:Seat n) (q:Gleam.Safe r (broken r t (silhouette σ Y.1)) l (σ.act i)):
    Rightful (halo m {i}) (gauge (T.arcs Y.1 σ) (X Y)) 1 (sphereRate*suitedFee r.count.val t):=by
 let τ:=silhouette σ Y.1; let F:= broken r t τ
 have hp(z:Seat n)(hz:z∈ Lattice.halo m {i}):Gleam.Safe r F (w+1) (σ.act z):=q.shift (by rw [separation_signed]; have he: separation i z≤ m:=(by simpa only [halo_spec,mem_singleton, exists_eq_left] using hz); omega)
 let S:=halo m {i}; apply (riotPort ..).2; rintro ⟨x,l⟩ u; obtain ⟨a,h⟩:= (mem_filter.mp u).2
 let P:= X Y; have hv:P (x,l)=Y.1 (x,l):= B.lamp Y.1 Y.2 (x,l) (Finset.disjoint_left.mpr fun i hi hh=>by
    obtain ⟨z,v,r₀⟩:= halo_spec.mp hh; have hz : z∈ S:=(mem_insert.mp v).elim (fun e=>e.symm ▸ a) (fun e=> (mem_singleton.mp e).symm ▸ h)
    have he: Gleam.Safe r F 0 (σ.act i):= (hp z hz).shift (by rw [separation_signed]; omega)
    exact closest T Y.1 σ e he hi) -- order possibly inferred
 let Z:= T.arcs Y.1 σ; let K:=(gauge Z Y.1) (x,l)
 rw [show (gauge _ _ (x,l))=K from ?_]; swap; · unfold K; change Z x * P _*_ = _; rw [hv]; rfl
 have hg: SU.group.chord K ≤ suitedFee r.count.val t:= T.clear_link Y.1 σ p _ ((hp x a).shift (by rw [separation_self]; omega))
 rw [Prod.norm_def]; apply (max_le (sphereRate_cost.bot K 1) (sphereRate_cost.top K 1)).trans; rw [BPress.chord.one]; exact mul_le_mul_of_nonneg_left hg sphereRate_cost.positive.le
#print axioms gleam_in_sleeve
open CF.Window Buffered
lemma snow_cost {l:ℕ}(B:Skye.Roof n b u w X)(p:0≤ t)(e:t ≤ b) {a C z d:ℝ}(v:0<C)(hu:0< d)(hz:0≤z)(Z:sphereRate*suitedFee r.count.val t≤z) (Y:Orbit n)(M:Tulip.Male)(ρ:m+w+1 ≤ l)(L:Checkers.Sow 4 n a C d)(f:u≤d)(q:l ≤ r.count.val/2) :
 let G:=T.arcs Y.1 σ
 let S:= FlatPaneP 4 M n
 entryBudget (spar 4 M (gauge G (X Y))-S) ≤ ((2*Real.exp (-(a*m))+m*4*z/d)*C)*(180*n.val^4)+2*C*180*(((Fintype.card (Site c)* largerBill r.count.val l + (broken r t (silhouette σ Y.1)).card*r.count.val^4:ℕ):ℝ)):=by
 intro G S; let U:=gauge G (X Y); let V:=spar 4 M U; let θ:= ((2*Real.exp (-(a*m))+(m:ℝ)*4*z/d)*C); have hU:Guard U d:=((Guard.cov (B.paid Y) G).shrink f); have hΩ:Guard (1:Pane n) d:=guard0 hu.le; let A:= broken r t (silhouette σ Y.1); let H:=univ.filter (fun i=>¬Gleam.Safe r A l i); let F:=univ.filter fun i:Seat n=> σ.act i∈H; let P:= modesIn n F
 have he(i:Single n): (∑ j, ‖(V-S) j i‖) ≤ θ+ if i∈ P then 2*C else 0:=by
    split
    · apply le_trans (b:=2*C) ?_ (le_add_of_nonneg_left (show 0 ≤ θ by unfold θ; positivity)); refine (sum_le_sum (g:=fun j=> ‖V j i‖+‖S j i‖) (fun j _=>norm_sub_le ..)).trans ?_; rw [sum_add_distrib,two_mul]; exact add_le_add (L.daylight false M U hU i) (L.daylight false M _ hΩ i)
    next p' =>
      let W:Support (More n):= {node i.1.1}; let R:= Matrix.of (fun j k:Single n=> if node k.1.1∈W then (V-S) j k else 0)
      have h:Gleam.Safe r A l (σ.act (node i.1.1)):= Classical.byContradiction fun y=> p' ((modes_at ..).mpr (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,y⟩⟩))
      have hv:= gleam_in_sleeve T σ l B ρ p e Y _ h
      have hx:= L.cross false M U _ hU hΩ W z m hz (fun i p=>(hv i p).trans Z) R (fun j k=>by unfold R; rw [Matrix.of_apply]; split; rotate_left; exact Or.inl rfl; exact Or.inr ⟨‹node k.1.1 ∈ W›,le_rfl⟩)
      rw [add_zero,show (∑ j:Single n,_)=∑ j,‖R j i‖ from ?_]; exact hx i; unfold R W; simp
 have hf: F.card≤H.card:=by
    rw [←card_image_of_injective F σ.act_injective]; exact card_le_card (image_subset_iff.mpr (fun v p=> (mem_filter.mp p).2))
 have hk:(P.card:ℝ) ≤ 180*((Fintype.card (Site c)* largerBill r.count.val l + (broken r t (silhouette σ Y.1)).card*r.count.val^4:ℕ):ℝ):=by
    rw [mul_comm]; have he:= Street.positions F; exact_mod_cast (he.trans (Nat.mul_le_mul_right _ (hf.trans (Regis.Head.cool_home T.odd_width q))))
 unfold entryBudget; rw [sum_comm]; apply (sum_le_sum (fun i _=>he i)).trans
 rw [sum_add_distrib,sum_ite,sum_const_zero,sum_const,sum_const,add_zero,filter_mem_eq_inter,univ_inter,card_univ]; simp only [nsmul_eq_mul,Pic.units_t]; unfold θ; nlinarith only [mul_le_mul_of_nonneg_left hk v.le]
#print axioms snow_cost
end Tiling
end YM.CF.Papyrus.Franc.SatinForce
