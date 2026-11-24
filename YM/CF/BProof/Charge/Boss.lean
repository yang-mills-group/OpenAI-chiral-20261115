import YM.CF.BProof.Charge.Cave

/-! Number of heavy terms paying each severe column. Scale by explicit power of M,
independent of period. Root reach for Hessian and high charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side} (Y:Yard s)(M:ℕ)(l:Tile s)(Z:Finset Y.Col)

def fork (b:Y.Col):= join (Y.v b.1) b.2 -- lower face of gap, may be N
lemma sep_by (x y:Site s){r:ℕ}(h:Circle.δ (time x) (time y) ≤r) (hp:Grid.dist (space x) (space y)≤ r):separation x y≤r:= by
 rw [← Micro.sep]; refine Grid.dist_le.mpr (fun i=> ?_); refine Fin.cases h (fun i=> (Grid.dist_le.mp hp i)) i
lemma charge_close {i:Y.Col}(h:Needs Y M l i): close Y (Lens Y l (M:=M)) i (3*M):=by unfold Needs at h; split at h; rw [h]; exact ⟨rfl,by simp [Grid.dist_self]⟩; exact h
lemma charge_loc (b:Y.Col)(h: Stove Y M l)(hp: Needs Y M l b): separation (fork Y b) (pilot l) ≤ Y.short+4*M:=by
 have e:= blamed Y M l h; obtain ⟨v,p⟩:= charge_close Y M l hp; change blame Y M l=b.1 at v; rw [v] at e
 obtain ⟨x,h,e⟩:=e; have he:Circle.δ (Y.v b.1) x≤ Y.short:= (Circle.δle _ Y.short x).2 (Or.inl h); have hx: Grid.dist (space (fork Y b)) (space (pilot l))≤3*M:=by unfold fork; rw [space_join,Grid.dist_symm]; exact p
 refine sep_by _ _ ((Cube.d_one_triangle (Y.v b.1) x _).trans (Nat.add_le_add he e)) (by omega)

def zone (b:Y.Col)(r:ℕ) := univ.filter (fun i=> close Y b i r)
@[simp] lemma zon {b i:Y.Col}{r}: i∈zone Y b r↔ close Y b i r:=by simp [zone]
def Gear (b:Y.Col):= univ.filter (fun l=> Stove Y M l ∧ Needs Y M l b)
@[simp] lemma engaged {b:Y.Col}{l:Tile s}: l∈Gear Y M b↔ Stove Y M l∧Needs Y M l b:=by simp [Gear]
abbrev multiplicity := Fintype.card Signed * Fintype.card PlaqAxes+Fintype.card PlaqAxes
lemma base_p (x:Site s) : (univ.filter fun a:Tile s=>pilot a=x).card≤multiplicity:=by
 let f(p:Sum (PlaqAxes) (Signed×PlaqAxes)):Tile s:=Sum.elim (fun a=>.inl (x,a)) (fun i=>.inr (i.1,i.2,x)) p
 apply le_trans (card_le_card (t:=univ.image f) (fun i (h:i∈ univ.filter _)=>?_))
 · apply card_image_le.trans; simp [multiplicity,add_comm]
 have he:pilot i=x:= (mem_filter.mp h).2; change i∈ image f univ; simp only [mem_image,mem_univ,true_and]; cases i with
 | inl p=> exact ⟨.inl p.2,by change Sum.inl (β:=Lam s) (x,p.2) = Sum.inl p; rw [← he]; rfl⟩
 | inr p=> exact ⟨.inr (p.1,p.2.1),by change Sum.inr (p.1,p.2.1,x)=_; rw [← he]; rfl⟩

def gearBound (D M:ℕ) := multiplicity*(2*(D+4*M)+1)^4
lemma gear_count (b:Y.Col): (Gear Y M b).card≤ gearBound Y.short M:=by
 let i:=Y.short+4*M; let F:= Grid.collar ({fork Y b}: Support s) i
 apply le_trans (card_le_card (t:=F.biUnion (fun i:Site s=>univ.filter (fun a:Tile s=>pilot a=i))) (fun x (h:x∈ Gear Y M b)=>?_))
 · apply Finset.card_biUnion_le.trans; apply le_trans (sum_le_sum (fun i h=>base_p i)); rw [sum_const,nsmul_eq_mul,mul_comm]; apply Nat.mul_le_mul_left; exact (Grid.collar_volume ..).trans_eq (by simp [i, Axis])
 obtain ⟨p,k⟩:= (engaged ..).1 h; apply mem_biUnion.mpr; exact ⟨_,Grid.collar_mem.mpr ⟨_,mem_singleton_self _,by rw [Grid.dist_symm]; exact charge_loc Y M x b p k⟩,show x∈univ.filter (fun q=> pilot q=pilot x) from by simp⟩

def Haz := Z.filter (Needs Y M l)
lemma haz_v : ¬Cave Y M l Z↔(Haz Y M l Z).Nonempty:=by rw [Cave.check]; simp [Nonempty,Haz,Finset.Nonempty]
def default' (S:Finset Y.Col) (i:Y.Col): Y.Col:=if h:S.Nonempty then h.choose else i -- Nonempty.choose
lemma default_mem (S: Finset Y.Col)(h:S.Nonempty)(i:Y.Col): default' Y S i∈S:=by rw [default',dif_pos h]; exact h.choose_spec
def bail (Z:Finset Y.Col):= default' Y (Haz Y M l Z) (Lens (M:=M) Y l)
def packs (b:Y.Col):= univ.filter (fun x:Tile s=> Stove Y M x∧ ¬ Cave Y M x Z ∧ bail Y M x Z=b)
lemma bail_hit (h:¬ Cave Y M l Z): bail Y M l Z∈ Z ∧ Needs Y M l (bail Y M l Z):= mem_filter.mp (default_mem _ _ ((haz_v ..).1 h) _)
lemma pack_v (b:Y.Col): (packs Y M Z b)⊆ Gear Y M b:=by intro l h; obtain ⟨u,h,e⟩:= (mem_filter.mp h).2; rw [← e]; exact (engaged ..).2 ⟨u,(bail_hit Y M l Z h).2⟩
lemma split_p : univ.filter (fun x=>Stove Y M x∧ ¬ Cave Y M x Z) = Z.biUnion (packs Y M Z):=by
 ext x; simp only [packs,mem_filter,true_and,mem_univ,mem_biUnion]; refine ⟨fun ⟨p,u⟩=> ⟨_,(bail_hit Y M x Z u).1,p,u,rfl⟩,fun ⟨v,h,p,q,h'⟩=> ⟨p,q⟩⟩
lemma packs_pair : (Z:Set _).PairwiseDisjoint (packs Y M Z):= by
 intro i _ j _ h; exact disjoint_left.mpr (fun _ p q=> h ((mem_filter.mp p).2.2.2.symm.trans (mem_filter.mp q).2.2.2))
lemma severe_rise (K: Room Y M)(b:Y.Door)(v:b.1∈ Z): Sum.inl (Y.rise b) ∈ packs Y M Z b.1:= by
 let l:Tile s:=.inl (Y.rise b); have p:Stove Y M l:=ripe Y _; have h: ¬ Cave Y M l Z:= fun h=> (rises_c Y M Z K b).1 h v; obtain ⟨z,hx⟩:=bail_hit Y M l Z h; unfold Needs at hx; rw [if_pos (show rising Y l from ⟨b,rfl⟩)] at hx; exact mem_filter.mpr ⟨mem_univ l,p,h,hx.trans (recognize Y l K p b rfl)⟩ -- tune
end YM.CF.BProof.Charge
