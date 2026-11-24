import YM.CF.BProof.Hero.Ride
import YM.CF.BProof.Angular.Vic
/-! Closed Mark belt lengths and extended square coverage. Use overlapping rXN mesh/entity
extension rather than special alignment of collar ends. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hero
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Grid
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}(a:Per s)(g:Ratio c s)(l:ℕ)
abbrev Aisle := (↑(BProof.strip a l):Set (Site s))
@[simp] lemma aisle_mem {x:Site s}: x∈ Aisle a l↔along a (time x)≤l:=mem_strip
-- extra margin for extending across sparse temporal cuts.
abbrev chip (x: Site s):= min (along a (time x)) (l-along a (time x))
abbrev Belt (u:ℕ):Set (Site s):={x| x∈Aisle a l ∧ chip a l x≤u}
abbrev life := l/5
abbrev BeltL := Belt a l (life l)
def room := Belt a l (life l+2*g.count.val)
def Width : Prop:= 200*g.count.val+200≤l
lemma belt_in {x:Site s}(v:x∈ BeltL a l) : x∈ room a g l:= ⟨v.1,v.2.trans (by omega)⟩
lemma accord {x:Site s}(k: x∈ Aisle a l) (p:x∉BeltL a l) : l/5<chip a l x:= lt_of_not_ge (fun h=>p ⟨k,h⟩)
lemma innerBand {x y:Site s} (e:2*l<s.val)(v: x∈ Aisle a l) (h:separation x y≤chip a l x):y∈ Aisle a l:=by
 obtain hl:= (aisle_mem ..).mp v; refine (aisle_mem ..).2 (Circle.deep a _ l (chip a l x) (min_le_left ..) ?_ ?_ _ ((Yard.time_jump ..).trans h)); have u:(chip a l x) ≤ l-along a (time x):=min_le_right ..; omega; have u:(chip a l x)≤l:=(min_le_left ..).trans hl; omega
lemma tend_le {x y:Site s}(hx:x∈ Aisle a l)(hy:y∈Aisle a l)(h:2*l<s.val) : along a (time y) ≤ along a (time x)+separation x y:=by
 let p:= along a (time x); let q:=along a (time y); have hp:p≤l:=mem_strip.mp hx; have hq:q≤l:=mem_strip.mp hy; change q≤p+_
 by_cases e:p≤q
 · have he : along (time x) (time y)+p=q:=by rw [add_comm]; exact (Circle.distance a (time x) (time y) e).symm
   have ht:= Yard.time_jump x y; rw [Circle.δ,d_sym,delta_eq] at ht; omega
 omega
lemma chip_le {x y:Site s}(hx:x∈ Aisle a l)(hy:y∈ Aisle a l)(h:2*l<s.val): chip a l y ≤ chip a l x+separation x y:=by
 have ht:=tend_le a l hx hy h; have hg:=tend_le a l hy hx h; rw [separation_comm] at hg; unfold chip; have hk:=mem_strip.mp hx; have hv:=mem_strip.mp hy; omega
lemma approach (x: Site s)(i:Axis) (hx:x∈ Aisle a l) (hy:x+step i∈ Aisle a l)(h:2*l<s.val): chip a l (x+step i) ≤ chip a l x+1 ∧ chip a l x ≤ chip a l (x+step i)+1 :=by
 have he:= chip_le a l hx hy h; have ht:= chip_le a l hy hx h; rw [separation_comm] at ht
 have hv:separation x (x+step i)≤1:= by rw [←Way, ←slide4]; exact Grid.near_slide ..
 exact ⟨by omega,by omega⟩

-- override; expand real assignment from all cells that stay in the slightly larger collar.
-- Edge crossing uses simultaneous licenses on shared layer.
def year(U:Bkg s)(A:Site s→Ballot)(x:Site s): Ballot:= if x∈BeltL a l then A x else expandX g (stack g (room a g l)) A U x
lemma turn_year (U:Bkg s)(A:Site s→Ballot)(x: Site s)(hx:x∈ BeltL a l): year a g l U A x=A x:=if_pos hx
@[measurability] lemma year_m : Measurable (uncurry (year a g l)):=by apply measurable_pi_lambda; intro x; unfold year uncurry; dsimp only; split_ifs; exact (measurable_pi_apply (X:=fun _:Site s=>Ballot) x).comp measurable_snd; exact (measurable_pi_apply x).comp (expandX_m g _)
lemma year_paid (U:Bkg s)(A:Site s→Ballot) (b:ℝ)(r:can b g.count)(W:Width g l)(h:2*l<s.val)(p:4≤c.val)(v: prie g.count ≤ b)(u: PaceX (room a g l) U A (prie g.count))(k: Wire.Flat SU.group U (Aisle a l) (tip g.count)): PaceX (Aisle a l) U (year a g l U A) b := by
 let B:= stack g (room a g l); let V:= stack g (Aisle a l); let X:= expandX g B A U; let Y:=year a g l U A; unfold Width at W
 have he := entersX g B A U b r V p (settleS g p _) (settleS g p _) (fun x hx=> pace_sub A U u (fun y hy=>hx y hy) le_rfl) (fun x hx=> flat_m U k (fun y hy=>hx y hy) le_rfl) -- tune
 have hz(x:Site s)(hx:x∈Aisle a l)(e: life l≤ chip a l x):Y x=X x:=by
    by_cases g':x∈ BeltL a l; · change year a g l _ _ _ = _; rw [turn_year _ _ _ _ _ _ g']; symm; apply enter_here; intro y hy; have hv:= Fence g _ _ _ (Grid.Entity.zero_proper g p x).1 hy; unfold life at *; have hi:y∈ Aisle a l:= innerBand a l h hx (hv.trans (by omega)); refine ⟨hi, (chip_le a l hx hi h).trans ?_⟩; exact Nat.add_le_add g'.2 hv -- tune
    exact if_neg g'
 intro x i hx hy; let y:=x+step i; change y∈Aisle a l at hy; have hf (a p q): Xd p (scaledV a q)=‖turn a q.val-p.val‖ := norm_sub_rev ..
 have hp:= approach a l x i hx hy h
 by_cases g':x∈ BeltL a l∧y∈BeltL a l
 · have hv:= (u x i (belt_in a g l g'.1) (belt_in a g l g'.2)).trans v; unfold EdgePrice at *; dsimp only at *; rw [turn_year a g l U A _ g'.1,turn_year a g l U A _ g'.2]; exact hv -- tune `dsimp *` huge
 push Not at g'; have hh: life l≤chip a l x∧life l≤chip a l y:=by
    by_cases ht:x∈BeltL a l
    · have hk:= accord a l hy (g' ht); change _≤ _+1 ∧ _ ≤ chip a l y+1 at hp; change chip a l y≤chip a l x+1 ∧ _ at hp; unfold life; omega
    have hk:= accord a l hx ht; change chip a l y≤chip a l x+1∧chip a l x ≤ chip a l y+1 at hp; unfold life; omega
 obtain ⟨z,q,t⟩:= Grid.Entity.entire g p x i; unfold EdgePrice; change ‖turn _ (Y y).val-(Y x).val‖≤ _; rw [hz x hx hh.1,hz y hy hh.2]; apply he (Platform z) ?_ x i q (by rw [←slide4]; exact t); intro s hs; have hu:= Fence g _ _ _ q hs; apply innerBand a l h hx (hu.trans ?_); apply le_trans (b:=life l) _ hh.1; unfold life; omega
lemma year_here (U V:Bkg s)(A B:Site s→Ballot)(x:Site s)(hx:x∈Aisle a l)(h:2*l<s.val)(p:4≤c.val)(e:Width g l)
 -- reads radius and for links both endpoints therein
 (u:Set.EqOn A B {y| y∈Aisle a l∧separation x y≤2*g.count.val})(v:Lattice.Agrees {y| y∈ Aisle a l∧separation x y≤2*g.count.val} U V):year a g l U A x=year a g l V B x:=by
 unfold year; split_ifs with H; · apply u (show x∈_ from ⟨hx,by simp⟩)
 let F:= Grid.Entity.chief g x; have hr: F.Mem g x:= (Grid.Entity.zero_proper g p x).1; have ht:= accord a l hx H; unfold Width at e
 have hv(y)(hy:F.Mem g y): y∈Aisle a l∧separation x y≤2*g.count.val:=by have hg:= Fence g F x y hr hy; exact ⟨innerBand a l h hx (hg.trans (by omega)),hg⟩
 exact expandX_eq g (stack g (room a g l)) A U F p _ (fun _ _=>Iff.rfl) B V (fun _ hy=> u (hv _ hy)) (fun i a b=> v i (hv _ a) (hv _ b)) hr
end YM.CF.BProof.Hero
