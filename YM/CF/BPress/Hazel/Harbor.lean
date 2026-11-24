import YM.CF.BPress.Hazel.Epoch
import YM.CF.BPress.Spin.Breach
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch
structure Rental where
 H : Side
 P : ℕ
 U : ℕ -- depth unsafe
 T : Side -- taper slack
 M : ℕ -- R_M final
 obscured : (P+1)*8≤ H.val
 home : H.val+2 ≤ U
 city : U+T.val + P + 2 ≤ M
variable (W:Rental)
namespace Rental
lemma one_H : 1 ≤ W.H.val:=W.H.property
lemma pu : W.P+1 ≤ W.U:=by have ht:= W.home; have he:= W.obscured; omega
lemma um : W.U ≤ W.M:=by have ht:= W.city; omega
lemma tm : W.T.val ≤ W.M:=by have ht:= W.city; omega
lemma hm : W.H.val+1 ≤ W.M:=by have ht:= W.home; exact le_trans (by omega : W.H.val+1 ≤ W.U) W.um
end Rental
-- require enough growth after selecting M. use R_M ≤ warm limit.
def Warm(B:BandWidth):= B.marked.val/10
structure Dusk (B:BandWidth)(R : Hangar s)(W:Rental):Prop where
 summer: W.M ≤ Warm B
 yieldr: W.M ≤ R.L.val
lemma halfway : Warm B ≤ Wealth.cloak B:=by unfold Warm Wealth.cloak; omega
variable {X:Bands s B}
def Local {R:Hangar s}(T: Seal (SiteX X R))(r:ℕ)(x: SiteX X R): Prop:=∃ a∈ T, x.1=a.1 ∧ delta a.2 x.2≤ r -- missing implicit
lemma plan_quote (R:Hangar s){p l : X.Hcols}(t:p.1=l.1) : own X R p=own X R l ↔ tang R p.2=tang R l.2:=by unfold own; simp only [t,Prod.mk.injEq,true_and]
variable (X)(R:Hangar s)(T: Seal (SiteX X R))
abbrev Good(T:Seal (SiteX X R))(r:ℕ)(p:X.Hcols): Prop:= ¬ Local T r (own X R p)
abbrev Near(T:Seal (SiteX X R))(r:ℕ)(x:Site s): Prop:= Local T r (plan X R x)
abbrev Bound(B:BandWidth):= Warm B -- tune
lemma local_0 (x:SiteX X R)(h:x∈ T)(r:ℕ): Local T r x:= ⟨x,h,rfl,by simp⟩
-- equivalence bay
lemma locale_eq {x:SiteX X R}{t:ℕ}: Local T t x↔ ∃ y∈T, x.1=y.1 ∧ x∈bay (shape X R) y t:=by
 refine ⟨?_,?_⟩; rintro ⟨y,p,g,h⟩; refine ⟨y,p,g,(bay_mem _).mpr (max_le ?_ h)⟩; rw [g,d_id]; omega; rintro ⟨y,t,h,b⟩; exact ⟨y,t,h,(le_max_right ..).trans (bay_mem ..|>.1 b)⟩
variable {X R W T} {r m:ℕ}{i:X.Index}
lemma local_m {x:SiteX X R}(h:Local T r x)(p:r≤ m): Local T m x:=by obtain ⟨x,g,h,v⟩:=h; exact ⟨x,g,h,v.trans p⟩
lemma local_f {x y: SiteX X R}(p: Local T r x)(e:x.1=y.1)(h: delta x.2 y.2≤ m): Local T (r+m) y:=by obtain ⟨z,t,p,u⟩:=p; exact ⟨z,t,e.symm.trans p,(delta_triangle _ x.2 _).trans (Nat.add_le_add u h)⟩
lemma local_quote {x y:X.Hcols}(h:Local T r (own X R x))(f:x.1=y.1)(u:delta x.2 y.2≤ R.L.val): Local T (r+1) (own X R y):= local_f h f (tang_rad R _ _ u)
lemma good_cc {x y:X.Hcols}(h:Good X R T (r+1) x)(t:x.1=y.1)(e:delta x.2 y.2 ≤ R.L.val): Good X R T r y:=fun u=>h (local_quote u t.symm ((delta_comm ..).le.trans e)) -- param tune
lemma good_m {x:X.Hcols}(h:Good X R T r x)(t:m≤r): Good X R T m x:= fun v=> h (local_m v t)

-- micro safety & collar activity
variable (X R W T)
def Danger (X:Bands s B)(R:Hangar s)(W:Rental)(T:Seal (SiteX X R)):= (univ : Seal (Site s)).filter fun x=> NearBlock X W.U x ∧ Near X R T 2 x
abbrev safe (X:Bands s B)(R:Hangar s)(W:Rental)(T:Seal (SiteX X R)):= (Danger X R W T)ᶜ
variable {X R W T}{p q x : Site s}
lemma touched_s : p∈ safe X R W T ↔ NearBlock X W.U p → Good X R T 2 (panel X p):=by simp only [safe,Danger,mem_compl,mem_filter,mem_univ,true_and]; tauto -- tune
lemma near_gap {x:Site s}(p:x∈halo r (X.gap i)): NearBlock X r x:=⟨i,(zone_of_halo ..).mp p⟩
lemma near_mature (p:x∈safe X R W T)(v:x∈halo r (X.gap i))(h:r≤W.U) : Good X R T 2 (panel X x):= touched_s.mp p (near_gap (Corona.halo_mono h le_rfl v)) -- missing variable
lemma far_good(h:Good X R T (r+1) (panel X p)) {i:X.Index} (a:q∈ halo m (X.gap i))(u:m≤ Wealth.cloak B)(t: separation p q≤ R.L.val)(v:town X p=i): Good X R T r (panel X q):= good_cc h (v.trans (moment_p X u a).symm) ((tail_sep ..).trans t)
lemma near_fit (t:r≤ Wealth.cloak B)(p: NearBlock X r x): x∈halo r (X.gap (town X x)):=by obtain ⟨i,g⟩:=p; have hp: x∈halo r (X.gap i):=(zone_of_halo ..).2 g; rw [moment_p X t hp]; exact hp -- tune x binder
section
variable (V:Dusk B R W)
include V
lemma patch_safe {r₀:ℕ} (t:p∈halo m (X.gap i))(g: r₀+m ≤ W.M)(h: Good X R T 3 (panel X p))(u:separation p q ≤ r₀) : q∈ halo (m+r₀) (X.gap i) ∧ q∈ safe X R W T := by
 have he:m+r₀≤ Wealth.cloak B:= by have ht:= V.summer.trans halfway; omega
 have ht:= crew_eq X u t; refine ⟨ht,touched_s.mpr (fun q=>far_good h ht he (u.trans (V.yieldr.trans' (by omega))) (moment_p X (by omega) t))⟩ -- tune
lemma packet (t:p∈safe X R W T)(v:p∈halo m (X.gap i))(h:m≤W.U)(u:separation p q≤W.P+1)(h':Good X R T 4 (panel X p))(l:m+W.P+1 ≤ W.M) : q∈halo (m+(W.P+1)) (X.gap i)∧ q∈safe X R W T∧ Good X R T 3 (panel X q):=by
 obtain ⟨t,v'⟩:= patch_safe V v (by omega) (good_m h' (by omega)) u; have hm:m+(W.P+1) ≤ Wealth.cloak B:=V.summer.trans halfway |>.trans' (by omega); refine ⟨t,v',far_good h' t hm (u.trans (by have he:=V.yieldr; omega)) (moment_p X (by omega) v)⟩ -- tune
-- D-changing activity: any within-distance T has near_depth & within ≤3 block. Membership name.
lemma hurt (p':p∈Lattice.halo W.T.val (Danger X R W T)): NearBlock X W.M p ∧ Near X R T 3 p := by
 obtain ⟨q,t,f⟩:=halo_spec.mp p'; obtain ⟨z,g⟩:= (mem_filter.mp t).2; have he:= V.summer.trans halfway; have hp:= near_fit (W.um.trans he) z; have hk: W.U+W.T.val≤ W.M:= by have he:= W.city; omega
 have hc:=crew_eq X f hp; exact ⟨near_gap (Corona.halo_mono hk le_rfl hc), local_quote g (moment_p X (hk.trans he) hc).symm ((tail_sep ..).trans (f.trans (W.tm.trans V.yieldr)))⟩
-- P neighborhood $≤ R_P$, retain profile. in fact if within halo of gap and good6 there, no Danger within. path substitutions. even in far mark maybe Good of other gap; when already beyond near-depth safe that case.
lemma beyond (p: Site s)(h:¬ (NearBlock X W.M p ∧ Near X R T 6 p)): p ∉ Lattice.halo W.T.val (Danger X R W T):= fun v=> h ⟨(hurt V v).1,local_m (hurt V v).2 (by norm_num)⟩
lemma good_retained (p:Site s)(g:Good X R T 3 (panel X p)): p∉ Lattice.halo W.T.val (Danger X R W T):= fun v=> g (hurt V v).2
end
-- bit sets
section ferm
variable {N:Side}(W:Rental){B:BandWidth}(X:Bands (More N) B)(R:Hangar (More N))(T: Seal (SiteX X R))
def Picks : Support N:= univ.filter fun x=> ¬ Welkin X (node x)∧ Good X R T 6 (Locale.panel X (node x))
lemma dark : Dark X (Picks X R T):= ⟨fun x h i u=> ((mem_filter.mp h).2).1 ⟨_,u⟩⟩
-- mask §B-Disz on Mark near and all unpicked unmarked; uniform cylinder expression.
def specialB : Support N:=univ.filter fun x=> Near X R T 6 (node x) ∧ NearBlock X W.M (node x)
lemma special {p: Site N}(x:p∈specialB W X R T): p∉ Picks X R T:= fun a=> ((mem_filter.mp a).2).2 ((mem_filter.mp x).2).1
lemma qualify {x :Site N} (p:x∉ Picks X R T) (t:¬ Welkin X (node x)): x∈specialB W X R T:= mem_filter.mpr ⟨mem_univ _,not_not.mp (fun a=> p (mem_filter.mpr ⟨mem_univ _,t,a⟩)), near_gap (halo_subset _ _ (noWel X t))⟩
lemma brew (V:Dusk B R W) : (specialB W X R T).card ≤ T.card * (4*6+1)^4 * (R.L.val^3 * (B.D + 2*W.M + 1)):=by
 let b:= shape X R; let c:=6; let F:= specialB W X R T; let S:= T.biUnion fun i=>bay b i 6; have he:F.image node ⊆ S.biUnion (fun i=> positions X R i W.M):= by
    intro i q; obtain ⟨x,t,rfl⟩:= mem_image.mp q; obtain ⟨x',v⟩:=(mem_filter.mp t).2; let i:= plan X R (node x); obtain ⟨y₀,u,p,e⟩:= (locale_eq X R T).1 x'; exact mem_biUnion.mpr ⟨i,mem_biUnion.mpr ⟨y₀,u,e⟩, mem_filter.mpr ⟨mem_univ _,rfl,v⟩⟩
 have ht:S.card≤T.card *(4*6+1)^4:= le_trans (card_biUnion_le) ((sum_le_sum (g:=fun _=>(4*6+1)^4) (fun i _=> capacity X R i 6)).trans_eq (by simp))
 apply le_trans _ (Nat.mul_le_mul_right _ ht); rw [← card_image_of_injective _ (Tenant.needle (N:=N))]; exact le_trans (card_le_card he) ((card_biUnion_le).trans ((sum_le_sum (fun i _=> pinned_cost X R i (V.summer.trans halfway))).trans_eq (by simp))) -- tune
end ferm
end YM.CF.BPress.Hazel
