import YM.SU5.MacroSix.TorRibbon

/-! # Actual advance of the mixed body within cover pocket accounts: ingredients

Here keep prices on the bare letters. For each tor we can recover the space
`torRibbon` exactly from values of these **cover** families (and these
support & Slot labels). On some earlier problems one anchor was priced in
a `Line` at the observation scale; this ribbon can use the whole pocket on
promotion, including mixing not authorized by the previous grammar. Proof
of paying for all sides adapts `Filigree.CLine_mend` to these costs.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
attribute [local instance] opCStarAlgebra

def living (K : Calibration) (b : Bool) (S : Finset Cover) : Submodule ℂ (Family K) :=
  Submodule.span ℂ {f|∃ x : Cover, ∃ i : SpinIdx, ∃ p : SU.Slot,
    i∈plusHalf ∧ nodeC x∈S ∧ wrapType p=b ∧ f=creation K x i p}
def dying (K : Calibration) (b : Bool) (S : Finset Cover) : Submodule ℂ (Family K) :=
  Submodule.span ℂ {f|∃ x : Cover, ∃ i : SpinIdx, ∃ p : SU.Slot,
    i∉plusHalf ∧ nodeC x∈S ∧ wrapType p=b ∧ f=removal K x i p}

def stamp (K : Calibration) (b : Bool) (X Y : Finset Cover) : Submodule ℂ (Family K) :=
  Submodule.span ℂ {f | ∃ a∈ living K b X, ∃ z ∈ dying K b Y, f=a*z ∨ f=z*a}

lemma Pinned.smul {N : Side} {b : Bool} {S : Support (More N)} {T : Finset (Single N)}
    {x : Ket (Single N)} (h : Pinned b S T x) (c : ℂ) : Pinned b S T (c • x) :=
  ⟨(map_smul _ _ _).trans (congrArg (fun a ↦ c • a) h.grade),
   (map_smul _ _ _).trans ((congrArg (fun a ↦ c • a) h.label_).trans (smul_comm c _ _)),
   (map_smul _ _ _).trans (congrArg (fun a ↦ c • a) h.far_)⟩

lemma Pinned.add {N : Side} {b : Bool} {S : Support (More N)} {T : Finset (Single N)}
    {x y : Ket (Single N)} (h : Pinned b S T x) (g : Pinned b S T y) : Pinned b S T (x+y) :=
  ⟨(map_add ..).trans (congrArg₂ (· + ·) h.grade g.grade),
   (map_add ..).trans ((congrArg₂ (· + ·) h.label_ g.label_).trans (smul_add ..).symm),
   (map_add ..).trans (congrArg₂ (· + ·) h.far_ g.far_)⟩

lemma Pinned.zero {N : Side} (b : Bool) (S : Support (More N)) (T : Finset (Single N)) :
    Pinned b S T 0 := ⟨map_zero _,(map_zero _).trans (smul_zero _).symm,map_zero _⟩

variable {K : Calibration} {b wide : Bool} {x y : Cover} {S X Y : Finset Cover}
  {f g : Family K}

lemma living_letter (K : Calibration) (x : Cover) (i : SpinIdx) (p : SU.Slot)
    (h : i∈plusHalf) (u : nodeC x∈ S) (v : wrapType p=b) : creation K x i p ∈ living K b S :=
  Submodule.subset_span (show _ ∈ _ from ⟨x,i,p,h,u,v,rfl⟩)

lemma dying_letter (K : Calibration) (x : Cover) (i : SpinIdx) (p : SU.Slot)
    (h : i∉plusHalf) (u : nodeC x∈ S) (v : wrapType p=b) : removal K x i p ∈ dying K b S :=
  Submodule.subset_span (show _ ∈ _ from ⟨x,i,p,h,u,v,rfl⟩)

lemma living_test (h : f∈ living K b S) : InTest K wide S true f :=
  Submodule.span_induction (p:=fun f _ ↦ InTest _ _ _ _ f)
    (by rintro f ⟨x,i,j,p,q,_,rfl⟩; exact .creator j p q) .zero
    (fun _ _ _ _ p q ↦ .add p q) (fun a _ _ h ↦ .smul a h) h
lemma dying_test (h : f∈ dying K b S) : InTest K wide S true f :=
  Submodule.span_induction (p:=fun f _ ↦ InTest _ _ _ _ f)
    (by rintro f ⟨x,i,j,p,q,_,rfl⟩; exact .remover j p q) .zero
    (fun _ _ _ _ p q ↦ .add p q) (fun a _ _ h ↦ .smul a h) h

-- use membership of actual x
lemma stamp_lr (h : f∈living K b X) (u : g∈dying K b Y) : f*g∈ stamp K b X Y :=
  Submodule.subset_span (show _ ∈ _ from ⟨f,h,g,u,Or.inl rfl⟩)
lemma stamp_rl (h : f∈living K b X) (u : g∈dying K b Y) : g*f∈ stamp K b X Y :=
  Submodule.subset_span (show _ ∈ _ from ⟨f,h,g,u,Or.inr rfl⟩)
lemma stamp_test (h : f∈ stamp K b X Y) (p : X⊆ S) (q : Y ⊆ S) : InTest K wide S false f := by
  refine Submodule.span_induction (p:=fun f _ ↦ InTest K wide S false f) ?_ .zero
    (fun _ _ _ _ p q ↦ .add p q) (fun a _ _ h ↦ .smul a h) h
  rintro f ⟨x,e,y,t,rfl|rfl⟩
  · exact .mul ((living_test e).mono p) ((dying_test t).mono q)
  exact .mul ((dying_test t).mono q) ((living_test e).mono p)

variable (N : Side)
lemma living_paid (h : f∈ living K b S) : ∃ x : Ket (Single (K.c N)),
    Pinned b (region S (K.c N)) (Tset (K.c N)) x ∧ ∀ W, f N W=create x := by
  let n := K.c N; let L := Tset n; let D := region S n
  refine Submodule.span_induction (p:=fun f _ ↦ ∃ x, Pinned b D L x ∧ ∀ W, f N W=create x) ?_
    ⟨0,Pinned.zero b D L,fun W ↦ (map_zero _).symm⟩ ?_ ?_ h
  · rintro f ⟨x,i,j,p,q,r,rfl⟩
    let y := basisC n x i j
    have hg := mem_image_of_mem (wrap (More n)) q
    have he : node (wrap n x) ∈ D := by rw [node_of]; exact hg
    exact ⟨y,(Pinned.basis ((mem_Tset _ _ _).2 p) r he).smul _,fun _ ↦ rfl⟩
  · rintro a t _ _ ⟨x,p,h⟩ ⟨y,q,e⟩; exact ⟨x+y,p.add q,fun W ↦
      (congrArg₂ (· + ·) (h W) (e W)).trans (map_add ..).symm⟩
  rintro c f _ ⟨x,p,h⟩; exact ⟨c • x,p.smul _,fun W ↦
    (congrArg (c • ·) (h W)).trans (map_smul ..).symm⟩

lemma dying_paid (h : f∈ dying K b S) : ∃ x : Ket (Single (K.c N)),
    Pinned b (region S (K.c N)) (Tset (K.c N))ᶜ x ∧ ∀ W, f N W=Fock.remove x := by
  let n := K.c N; let L := (Tset n)ᶜ; let D := region S n
  refine Submodule.span_induction (p:=fun f _ ↦ ∃ x, Pinned b D L x ∧ ∀ W, f N W=Fock.remove x) ?_
    ⟨0,Pinned.zero b D L,fun W ↦ by change 0=star (create _); rw [map_zero,star_zero]⟩ ?_ ?_ h
  · rintro f ⟨x,i,j,p,q,r,rfl⟩
    let y := basisC n x i j; have ht : Lifted.index n x i j ∈ L :=
      mem_compl.mpr (mt ((mem_Tset ..).1) p)
    have hg := mem_image_of_mem (wrap (More n)) q
    have he : node (wrap n x) ∈ D := by rw [node_of]; exact hg
    exact ⟨y,(Pinned.basis ht r he).smul _,fun _ ↦ rfl⟩
  · rintro a t _ _ ⟨x,p,h⟩ ⟨y,q,e⟩; refine ⟨x+y,p.add q,fun W ↦ ?_⟩
    simp_rw [Pi.add_apply,h W,e W,Fock.remove,map_add,star_add]
  rintro c f _ ⟨x,p,h⟩; refine ⟨star c • x,p.smul _,fun W ↦ ?_⟩
  simp_rw [Pi.smul_apply,h W,Fock.remove,map_smul,star_smul,star_star]

lemma stamp_paid (h : f∈ stamp K b X Y) :
    ∃ A∈ torRibbon b (region X (K.c N)) (region Y (K.c N)), ∀ W, f N W=A := by
  let L := torRibbon b (region X (K.c N)) (region Y (K.c N))
  refine Submodule.span_induction (p:=fun f _ ↦ ∃ A ∈ L, ∀ W, f N W=A) ?_
    ⟨0,L.zero_mem,fun _ ↦ rfl⟩ ?_ ?_ h
  · rintro f ⟨x,p,y,q,e⟩
    obtain ⟨i,hi,u⟩ := living_paid N p; obtain ⟨j,hj,w⟩ := dying_paid N q
    rcases e with rfl|rfl
    · exact ⟨_,torRibbon_lr hi hj,fun W ↦ congrArg₂ (· * ·) (u W) (w W)⟩
    exact ⟨_,torRibbon_rl hi hj,fun W ↦ congrArg₂ (· * ·) (w W) (u W)⟩
  · rintro a t _ _ ⟨x,p,h⟩ ⟨y,q,e⟩; exact ⟨x+y,L.add_mem p q,fun W ↦
      congrArg₂ (· + ·) (h W) (e W)⟩
  rintro c f _ ⟨x,p,h⟩; exact ⟨c • x,L.smul_mem _ p,fun W ↦ congrArg (c • ·) (h W)⟩

-- at each N: one tor really identifies the cover expansion of each tor monomial (priced with its own stencil). Adapt LiftMark.nodeIn and Filigree.nodeSend
private lemma nodeSend {n:Side}{o:Cover}{p:Site n}(h:(node p)=wrap (More n) o) : ∃ c: Cover,o=nodeC c ∧ wrap n c=p:=by
 let u:=nodeC (Rush.natural p); let k:= periods (More n) o-periods (More n) u
 let b:= Rush.natural p + n.val • k
 have hp:wrap (More n) o=wrap (More n) u:= by unfold u; rw [←node_of,Rush.nat_true]; exact h.symm
 have he:o=u+(More n).val • k:=by
    have e:= carrying (More n) o; have g:=carrying (More n) u
    unfold k; rw [hp] at e; rw [smul_sub]; calc
    _ = (natural ((wrap (More n)) u)+(More n).val • periods (More n) u) + ((More n).val • periods (More n) o - (More n).val • periods (More n) u) := e.symm.trans (by abel)
    _ = _:= by rw [g]
 have hf:o=nodeC b:=by rw [he,show (More n).val= (2:ℕ)*n.val from (mul_comm ..),mul_smul]; unfold u b nodeC; rw [smul_add]; abel
 exact ⟨b,hf,Tenant.needle (by rw [node_of,←hf]; exact h.symm)⟩

variable (K)
local notation "n" => K.c N

def adoptedAt (Q : Submodule ℂ (Family K)) : Submodule ℂ (FC (Single (K.c N))) where
  carrier := {A | ∃ x ∈ Q, ∀ i, x N i=A}
  zero_mem' := ⟨0,Q.zero_mem,fun _ ↦ rfl⟩
  add_mem' := by rintro _ _ ⟨x,p,h⟩ ⟨y,q,e⟩; exact ⟨x+y,Q.add_mem p q,fun W ↦
      congrArg₂ (· + ·) (h W) (e W)⟩
  smul_mem' := by rintro a f ⟨x,p,h⟩; exact ⟨a • x,Q.smul_mem _ p,fun W ↦ congrArg (a • ·) (h W)⟩

lemma Pinned.position {N : Side} {X : Finset Cover} {Y : Finset (Single N)}
    {x : Ket (Single N)} (h : Pinned b (region X N) Y x) {i : Single N} (u : x.ofLp i ≠ 0) :
    i ∈ Y ∧ wrapType i.2=b ∧ ∃ a : Cover, nodeC a∈X ∧ i.1.1=wrap N a := by
  have hx : node i.1.1 ∈ region X N := (modes_at ..).1 (Classical.byContradiction
    (fun t ↦ u ((within_test ..).1 h.far_ i t)))
  obtain ⟨y,e,w⟩ := mem_image.mp hx
  obtain ⟨a,rfl,hv⟩ := nodeSend w.symm
  exact ⟨Classical.byContradiction (fun t ↦ u ((within_test ..).1 h.grade i t)),
    center_coords.mp h.label_ _ u,a,e,hv.symm⟩

lemma living_adopts {x : Ket (Single (K.c N))} (h : Pinned b (region S (K.c N)) (Tset (K.c N)) x) :
    create x ∈ adoptedAt K N (living K b S) := by
  let U := living K b S
  nth_rw 1 [←basis_expand x]
  rw [map_sum]; apply Submodule.sum_mem
  intro i _; rw [map_smul]
  by_cases v : x.ofLp i = 0; · rw [v,zero_smul]; apply Submodule.zero_mem
  apply Submodule.smul_mem; obtain ⟨p,q,a,e,w⟩ := Pinned.position h v
  obtain ⟨⟨y,i⟩,j⟩ := i; change y= wrap n a at w; subst y
  have hp : i∈plusHalf := (mem_Tset ..).1 p; let f := creation K a i j; let k := Lifted.winding n a
  refine ⟨k • f,U.smul_mem _ (living_letter K a i j hp e q),fun V ↦ ?_⟩
  have hw : k*k=1 := fee_one _
  change k • create (k • _) = _; rw [map_smul,smul_smul,hw,one_smul]; rfl

lemma dying_adopts {x : Ket (Single (K.c N))} (h : Pinned b (region S (K.c N)) (Tset (K.c N))ᶜ x) :
    Fock.remove x ∈ adoptedAt K N (dying K b S) := by
  let U := dying K b S
  nth_rw 1 [←basis_expand x]
  unfold Fock.remove; rw [map_sum,star_sum]; apply Submodule.sum_mem
  intro i _; rw [map_smul,star_smul]
  by_cases v : x.ofLp i=0; · rw [v,star_zero,zero_smul]; exact Submodule.zero_mem _
  apply Submodule.smul_mem; obtain ⟨p,q,a,e,w⟩ := Pinned.position h v
  obtain ⟨⟨y,i⟩,j⟩ := i; change y= wrap n a at w; subst y
  have hp : i∉plusHalf := mt ((mem_Tset ..).2) (mem_compl.mp p); let f := removal K a i j
  let k := Lifted.winding n a
  refine ⟨k • f,U.smul_mem _ (dying_letter K a i j hp e q),fun V ↦ ?_⟩
  have hw : k*k=1 := fee_one _
  change k • star (create (k • _)) = _; rw [map_smul,star_smul,show star k=k from fee_real _,
    smul_smul,hw,one_smul]; rfl

lemma adopted_tor {A : FC (Single (K.c N))}
    (h : A ∈ torRibbon b (region X (K.c N)) (region Y (K.c N))) :
    ∃ f∈ stamp K b X Y, ∀ W, f N W=A := by
  change A ∈ adoptedAt K N (stamp K b X Y)
  apply (Submodule.span_le.mpr ?_ : torRibbon b _ _ ≤ _) h
  rintro A ⟨x,y,p,q,e⟩
  obtain ⟨f,u,h⟩ := living_adopts K N p; obtain ⟨F,v,w⟩ := dying_adopts K N q
  rcases e with rfl|rfl
  · exact ⟨f*F,stamp_lr u v,fun W ↦ congrArg₂ (· * ·) (h W) (w W)⟩
  exact ⟨F*f,stamp_rl u v,fun W ↦ congrArg₂ (· * ·) (w W) (h W)⟩
end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms stamp_paid
#print axioms adopted_tor
end YM.CF.Buffered.Afterglow.Pockets
