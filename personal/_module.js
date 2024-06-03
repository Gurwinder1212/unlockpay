function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function set_custom_element_data(node, prop, value) {
    if (prop in node) {
        node[prop] = typeof node[prop] === 'boolean' && value === '' ? true : value;
    }
    else {
        attr(node, prop, value);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let script0;
	let script0_src_value;
	let script1;
	let script1_src_value;
	let link4;
	let link4_href_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			script0 = element("script");
			script1 = element("script");
			link4 = element("link");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1mxt64k', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { type: true, src: true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", { src: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);

			link4 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			meta2 = claim_element(head_nodes, "META", { charset: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Fraunces:wght@700&family=IBM+Plex+Mono:wght@500;700&family=Work+Sans&display=swap");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "stylesheet");
			attr(link3, "type", "text/css");
			attr(link3, "href", "https://cdn.jsdelivr.net/npm/toastify-js/src/toastify.min.css");
			attr(script0, "type", "text/javascript");
			if (!src_url_equal(script0.src, script0_src_value = "https://cdn.jsdelivr.net/npm/toastify-js")) attr(script0, "src", script0_src_value);
			if (!src_url_equal(script1.src, script1_src_value = "https://unpkg.com/@lottiefiles/lottie-player@1.5.7/dist/lottie-player.js")) attr(script1, "src", script1_src_value);
			attr(link4, "rel", "icon");
			attr(link4, "type", "image/png");
			attr(link4, "sizes", "32x32");
			attr(link4, "href", link4_href_value = /*favicon*/ ctx[0].url);
			document.title = "UNLOK Loyalty | Personal";
			attr(meta2, "charset", "UTF-8");
			attr(meta3, "name", "description");
			attr(meta3, "content", "Unleash the Power of Blockchain Rewards");
			attr(meta4, "name", "keywords");
			attr(meta4, "content", "Blockchain, Crypto, Cryptocurrency, Unlok, Rewards, Staking, Loyalty Program, Earn, Redeem");
			attr(meta5, "name", "author");
			attr(meta5, "content", "Unlok Loyalty");
			attr(meta6, "name", "viewport");
			attr(meta6, "content", "width=device-width, initial-scale=1.0");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(document.head, link4);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link4_href_value !== (link4_href_value = /*favicon*/ ctx[0].url)) {
				attr(link4, "href", link4_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(script0);
			detach(script1);
			detach(link4);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (254:35) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (252:10) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (259:10) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { id: true, class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

// (273:35) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (271:10) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (289:8) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*site_nav_button*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "primary-small-button");
			attr(a, "id", "nav");
			attr(a, "href", a_href_value = /*site_nav_button*/ ctx[2].url);
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-jc1u8d");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*window, site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t1_value !== (t1_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a_href_value !== (a_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (292:14) {#each site_nav as { link }}
function create_each_block(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);

			a = claim_element(h6_nodes, "A", {
				id: true,
				class: true,
				active: true,
				href: true
			});

			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "active", "true");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let header;
	let div3;
	let div2;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*site_nav_button*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: {
				height: "37",
				icon: "eva:menu-outline",
				style: "color:black;"
			}
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			header = claim_element(div4_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { style: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-jc1u8d");
			attr(a1, "class", "primary-small-button");
			attr(a1, "id", "nav");
			attr(a1, "href", a1_href_value = /*site_nav_button*/ ctx[2].url);
			set_style(nav, "display", "flex");
			set_style(nav, "align-items", "center");
			attr(nav, "class", "svelte-jc1u8d");
			attr(div0, "class", "desktop-nav svelte-jc1u8d");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-jc1u8d");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-jc1u8d");
			attr(div2, "class", "section-container svelte-jc1u8d");
			attr(div3, "class", "header-container svelte-jc1u8d");
			attr(header, "class", "svelte-jc1u8d");
			attr(div4, "class", "section");
			attr(div4, "id", "section-ef3a7f45");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*window, site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t2_value !== (t2_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a1_href_value !== (a1_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let mobileNavOpen = false;

	function toggleMobileNav() {
		$$invalidate(3, mobileNavOpen = !mobileNavOpen);

		if (mobileNavOpen) {
			document.body.style.overflow = 'hidden';
		} else {
			document.body.style.overflow = 'unset';
		}
	}

	const click_handler = () => toggleMobileNav();
	const click_handler_1 = () => toggleMobileNav();

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(2, site_nav_button = $$props.site_nav_button);
	};

	return [
		logo,
		site_nav,
		site_nav_button,
		mobileNavOpen,
		toggleMobileNav,
		favicon,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 5,
			logo: 0,
			site_nav: 1,
			site_nav_button: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div8;
	let section;
	let div7;
	let div6;
	let div5;
	let div0;
	let h10;
	let t0;
	let t1;
	let div1;
	let h11;
	let t2;
	let t3;
	let div2;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t4;
	let h6;
	let t5;
	let t6;
	let div4;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t7;
	let div3;
	let lottie_player0;
	let lottie_player0_src_value;
	let t8;
	let lottie_player1;
	let lottie_player1_src_value;
	let t9;
	let lottie_player2;
	let lottie_player2_src_value;
	let t10;
	let img2;
	let img2_src_value;
	let img2_alt_value;

	return {
		c() {
			div8 = element("div");
			section = element("section");
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			div0 = element("div");
			h10 = element("h1");
			t0 = text(/*hero_title1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			h11 = element("h1");
			t2 = text(/*hero_title2*/ ctx[1]);
			t3 = space();
			div2 = element("div");
			img0 = element("img");
			t4 = space();
			h6 = element("h6");
			t5 = text(/*hero_description*/ ctx[2]);
			t6 = space();
			div4 = element("div");
			img1 = element("img");
			t7 = space();
			div3 = element("div");
			lottie_player0 = element("lottie-player");
			t8 = space();
			lottie_player1 = element("lottie-player");
			t9 = space();
			lottie_player2 = element("lottie-player");
			t10 = space();
			img2 = element("img");
			this.h();
		},
		l(nodes) {
			div8 = claim_element(nodes, "DIV", { class: true, id: true });
			var div8_nodes = children(div8);
			section = claim_element(div8_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div7 = claim_element(section_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div0 = claim_element(div5_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h10 = claim_element(div0_nodes, "H1", { class: true });
			var h10_nodes = children(h10);
			t0 = claim_text(h10_nodes, /*hero_title1*/ ctx[0]);
			h10_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div5_nodes);
			div1 = claim_element(div5_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h11 = claim_element(div1_nodes, "H1", { class: true });
			var h11_nodes = children(h11);
			t2 = claim_text(h11_nodes, /*hero_title2*/ ctx[1]);
			h11_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			div2 = claim_element(div5_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			img0 = claim_element(div2_nodes, "IMG", { class: true, src: true, alt: true });
			t4 = claim_space(div2_nodes);
			h6 = claim_element(div2_nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			t5 = claim_text(h6_nodes, /*hero_description*/ ctx[2]);
			h6_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			img1 = claim_element(div4_nodes, "IMG", { class: true, src: true, alt: true });
			t7 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);

			lottie_player0 = claim_element(div3_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player0).forEach(detach);
			div3_nodes.forEach(detach);
			t8 = claim_space(div4_nodes);

			lottie_player1 = claim_element(div4_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player1).forEach(detach);
			t9 = claim_space(div4_nodes);

			lottie_player2 = claim_element(div4_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player2).forEach(detach);
			t10 = claim_space(div4_nodes);
			img2 = claim_element(div4_nodes, "IMG", { class: true, src: true, alt: true });
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h10, "class", "svelte-6dussa");
			attr(div0, "class", "hero-text-container1 svelte-6dussa");
			attr(h11, "class", "svelte-6dussa");
			attr(div1, "class", "hero-text-container2 svelte-6dussa");
			attr(img0, "class", "hero-image-1 svelte-6dussa");
			if (!src_url_equal(img0.src, img0_src_value = /*hero_image_1*/ ctx[3].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*hero_image_1*/ ctx[3].alt);
			attr(h6, "class", "h650 svelte-6dussa");
			attr(div2, "class", "hero-feature-container svelte-6dussa");
			attr(img1, "class", "hero-image-2 svelte-6dussa");
			if (!src_url_equal(img1.src, img1_src_value = /*hero_image_2*/ ctx[4].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*hero_image_2*/ ctx[4].alt);
			set_custom_element_data(lottie_player0, "autoplay", "");
			set_custom_element_data(lottie_player0, "loop", "");
			set_custom_element_data(lottie_player0, "mode", "normal");
			set_custom_element_data(lottie_player0, "class", "lottie-4 svelte-6dussa");
			if (!src_url_equal(lottie_player0.src, lottie_player0_src_value = flyingPigLottie)) set_custom_element_data(lottie_player0, "src", lottie_player0_src_value);
			attr(div3, "class", "pink-box svelte-6dussa");
			set_custom_element_data(lottie_player1, "autoplay", "");
			set_custom_element_data(lottie_player1, "loop", "");
			set_custom_element_data(lottie_player1, "mode", "normal");
			set_custom_element_data(lottie_player1, "class", "lottie-2 svelte-6dussa");
			if (!src_url_equal(lottie_player1.src, lottie_player1_src_value = foodorderDeliveryLottie)) set_custom_element_data(lottie_player1, "src", lottie_player1_src_value);
			set_custom_element_data(lottie_player2, "autoplay", "");
			set_custom_element_data(lottie_player2, "loop", "");
			set_custom_element_data(lottie_player2, "mode", "normal");
			set_custom_element_data(lottie_player2, "class", "lottie-3 svelte-6dussa");
			if (!src_url_equal(lottie_player2.src, lottie_player2_src_value = honeymoonTravellingLottie)) set_custom_element_data(lottie_player2, "src", lottie_player2_src_value);
			attr(img2, "class", "lottie-1 svelte-6dussa");
			if (!src_url_equal(img2.src, img2_src_value = /*temp_image*/ ctx[5].url)) attr(img2, "src", img2_src_value);
			attr(img2, "alt", img2_alt_value = /*temp_image*/ ctx[5].alt);
			attr(div4, "class", "hero-image-2-wrapper svelte-6dussa");
			attr(div5, "class", "hero-container svelte-6dussa");
			attr(div6, "class", "header-wrapper svelte-6dussa");
			attr(div7, "class", "header-container svelte-6dussa");
			attr(section, "class", "svelte-6dussa");
			attr(div8, "class", "section");
			attr(div8, "id", "section-13d62e13");
		},
		m(target, anchor) {
			insert_hydration(target, div8, anchor);
			append_hydration(div8, section);
			append_hydration(section, div7);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div0);
			append_hydration(div0, h10);
			append_hydration(h10, t0);
			append_hydration(div5, t1);
			append_hydration(div5, div1);
			append_hydration(div1, h11);
			append_hydration(h11, t2);
			append_hydration(div5, t3);
			append_hydration(div5, div2);
			append_hydration(div2, img0);
			append_hydration(div2, t4);
			append_hydration(div2, h6);
			append_hydration(h6, t5);
			append_hydration(div5, t6);
			append_hydration(div5, div4);
			append_hydration(div4, img1);
			append_hydration(div4, t7);
			append_hydration(div4, div3);
			append_hydration(div3, lottie_player0);
			append_hydration(div4, t8);
			append_hydration(div4, lottie_player1);
			append_hydration(div4, t9);
			append_hydration(div4, lottie_player2);
			append_hydration(div4, t10);
			append_hydration(div4, img2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*hero_title1*/ 1) set_data(t0, /*hero_title1*/ ctx[0]);
			if (dirty & /*hero_title2*/ 2) set_data(t2, /*hero_title2*/ ctx[1]);

			if (dirty & /*hero_image_1*/ 8 && !src_url_equal(img0.src, img0_src_value = /*hero_image_1*/ ctx[3].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*hero_image_1*/ 8 && img0_alt_value !== (img0_alt_value = /*hero_image_1*/ ctx[3].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*hero_description*/ 4) set_data(t5, /*hero_description*/ ctx[2]);

			if (dirty & /*hero_image_2*/ 16 && !src_url_equal(img1.src, img1_src_value = /*hero_image_2*/ ctx[4].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*hero_image_2*/ 16 && img1_alt_value !== (img1_alt_value = /*hero_image_2*/ ctx[4].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*temp_image*/ 32 && !src_url_equal(img2.src, img2_src_value = /*temp_image*/ ctx[5].url)) {
				attr(img2, "src", img2_src_value);
			}

			if (dirty & /*temp_image*/ 32 && img2_alt_value !== (img2_alt_value = /*temp_image*/ ctx[5].alt)) {
				attr(img2, "alt", img2_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div8);
		}
	};
}

let foodorderDeliveryLottie = '{"v":"5.5.7","meta":{"g":"LottieFiles AE 0.1.20","a":"","k":"","d":"","tc":""},"fr":25,"ip":0,"op":100,"w":1000,"h":1000,"nm":"FFood_02_Big_Bag_04","ddd":0,"assets":[],"layers":[{"ddd":0,"ind":1,"ty":4,"nm":"Bubbles 2","parent":6,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[180.253,261.927,0],"ix":2},"a":{"a":0,"k":[134.491,156.876,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.417,0],[0,9.416],[9.416,0]],"o":[[0,9.416],[9.416,0],[0,-9.416],[-9.417,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[159.864,252.641],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[190.198,228.143],"to":[0,0],"ti":[0,0]},{"t":100,"s":[159.864,252.641]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.416,0],[0,9.417],[9.416,0]],"o":[[0,9.417],[9.416,0],[0,-9.416],[-9.416,0]],"v":[[-17.05,-0.001],[0,17.049],[17.05,-0.001],[0,-17.049]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[67.05,246.703],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[65.574,226.657],"to":[0,0],"ti":[0,0]},{"t":100,"s":[67.05,246.703]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":3,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.417,0],[0,9.416],[9.416,0]],"o":[[0,9.416],[9.416,0],[0,-9.416],[-9.417,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[64.87,177.286],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[69.654,147.401],"to":[0,0],"ti":[0,0]},{"t":100,"s":[64.87,177.286]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":3,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.417],[-9.417,0],[0,9.416],[9.416,0]],"o":[[0,9.416],[9.416,0],[0,-9.417],[-9.417,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[68.87,105.299],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[54.949,63.92],"to":[0,0],"ti":[0,0]},{"t":100,"s":[68.87,105.299]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":3,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.416,0],[0,9.417],[9.416,0]],"o":[[0,9.417],[9.416,0],[0,-9.416],[-9.416,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[182.075,187.895],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[154.289,159.557],"to":[0,0],"ti":[0,0]},{"t":100,"s":[182.075,187.895]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":3,"cix":2,"bm":0,"ix":5,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.416,0],[0,9.416],[9.416,0]],"o":[[0,9.416],[9.416,0],[0,-9.416],[-9.416,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[192.529,72.05],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[202.787,62.315],"to":[0,0],"ti":[0,0]},{"t":100,"s":[192.529,72.05]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 6","np":3,"cix":2,"bm":0,"ix":6,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-9.416],[-9.417,0],[0,9.417],[9.416,0]],"o":[[0,9.417],[9.416,0],[0,-9.416],[-9.417,0]],"v":[[-17.05,0],[0,17.05],[17.05,0],[0,-17.05]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[171.933,128],"to":[0,0],"ti":[0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[154.672,99.539],"to":[0,0],"ti":[0,0]},{"t":100,"s":[171.933,128]}],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 7","np":3,"cix":2,"bm":0,"ix":7,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":2,"ty":4,"nm":"Tea Cap Top 2","parent":6,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[175.933,50.041,0],"ix":2},"a":{"a":0,"k":[190.921,261.046,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.865,-0.001],[0,0],[0,3.866],[0,0],[-3.865,0.001],[0,0],[-0.001,-3.867],[0,0]],"o":[[0,0],[-3.866,0.001],[0,0],[-0.001,-3.866],[0,0],[3.866,-0.001],[0,0],[0.001,3.866]],"v":[[133.922,19.034],[-133.914,19.076],[-140.915,12.077],[-140.919,-12.033],[-133.921,-19.034],[133.915,-19.076],[140.917,-12.077],[140.92,12.032]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[0.62400004069,0.991999966491,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[190.921,241.97],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":3,"ty":4,"nm":"Straw 2","parent":6,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":12,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":27,"s":[-1]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":37,"s":[4]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":47,"s":[-3]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":57,"s":[2]},{"i":{"x":[0.764],"y":[0.66]},"o":{"x":[0.478],"y":[0]},"t":67,"s":[-1]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-1.765]},"t":77,"s":[0.5]},{"t":92,"s":[0]}],"ix":10},"p":{"a":0,"k":[154.951,369.562,0],"ix":2},"a":{"a":0,"k":[169.016,580.566,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[-61.789,265.283],[-37.054,-248.091],[61.789,-265.283]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[230.805,315.283],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":4,"ty":4,"nm":"Tea Cap 2","parent":2,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[190.921,222.901,0],"ix":2},"a":{"a":0,"k":[190.921,222.901,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,1.587],[-68.881,0],[0,-57.314],[1.587,0]],"o":[[-1.587,0],[0,-57.314],[68.881,0],[0,1.587],[0,0]],"v":[[-122.047,53.408],[-124.92,50.534],[0,-53.408],[124.92,50.534],[122.046,53.408]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[190.921,169.493],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[33.239,18.698],[16.928,0],[4.329,-54.073],[0,0],[0,1.587]],"o":[[-14.735,-5.099],[-66.062,0],[0,0],[1.587,0],[0,-35.825]],"v":[[58.655,-40.563],[10.843,-48.482],[-113.788,48.482],[110.914,48.482],[113.788,45.609]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[0.62400004069,0.991999966491,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[202.053,174.419],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[68.881,0],[0,-57.314],[-1.587,0],[0,0],[0,1.587]],"o":[[-68.881,0],[0,1.587],[0,0],[1.587,0],[0,-57.314]],"v":[[0,-53.408],[-124.92,50.535],[-122.047,53.408],[122.046,53.408],[124.92,50.535]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,1,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[190.921,169.493],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":5,"ty":4,"nm":"Tea 2","parent":6,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[176.088,402.769,0],"ix":2},"a":{"a":0,"k":[170.58,326.992,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":1,"k":[{"i":{"x":0.782,"y":1},"o":{"x":0.861,"y":0},"t":10,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-120.011,-138.459],[-120.58,-138.429],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.58,-138.466],[119.986,-138.497]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":25,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-119.88,-140.956],[-120.449,-140.926],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.109,-129.478],[119.515,-129.509]],"c":true}]},{"i":{"x":0.491,"y":1},"o":{"x":0.527,"y":0},"t":35,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-119.739,-117.118],[-120.308,-117.088],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.403,-159.485],[119.809,-159.516]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":45,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-121.823,-155.871],[-122.392,-155.841],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[118.996,-121.556],[118.402,-121.587]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":55,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-120.572,-132.619],[-121.141,-132.589],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[119.84,-144.314],[119.246,-144.345]],"c":true}]},{"i":{"x":0.764,"y":0.716},"o":{"x":0.478,"y":0},"t":65,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-121.323,-146.57],[-121.892,-146.54],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[119.333,-130.659],[118.739,-130.69]],"c":true}]},{"i":{"x":0.442,"y":1},"o":{"x":0.272,"y":0.981},"t":75,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-119.824,-131.421],[-120.393,-131.391],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.227,-141.481],[119.633,-141.512]],"c":true}]},{"t":90,"s":[{"i":[[0,0],[0.187,-0.018],[0,0],[-14.167,0.002],[0,0],[-1.063,14.128],[0,0],[0.201,0]],"o":[[-0.192,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.195,-0.019],[0,0]],"v":[[-120.011,-138.459],[-120.58,-138.429],[-101.554,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.58,-138.466],[119.986,-138.497]],"c":true}]}],"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[170.58,188.497],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":1,"k":[{"i":{"x":0.782,"y":1},"o":{"x":0.861,"y":0},"t":10,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[106.415,-124.885],[-99.958,-124.851],[-106.142,-118.18],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":25,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[105.944,-115.897],[-99.828,-127.348],[-106.012,-120.677],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.491,"y":1},"o":{"x":0.527,"y":0},"t":35,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[106.238,-145.904],[-99.686,-103.51],[-105.87,-96.839],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":45,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[104.831,-107.975],[-101.771,-142.264],[-107.955,-135.593],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":55,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[105.675,-130.732],[-100.52,-119.012],[-106.704,-112.341],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.764,"y":0.716},"o":{"x":0.478,"y":0},"t":65,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[105.169,-117.078],[-101.27,-132.963],[-107.454,-126.292],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"i":{"x":0.442,"y":1},"o":{"x":0.272,"y":0.981},"t":75,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[106.062,-127.9],[-99.771,-117.813],[-105.955,-111.142],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]},{"t":90,"s":[{"i":[[-1.062,14.128],[0,0],[0,0],[-0.273,-3.6],[0,0],[-0.375,0],[0,0]],"o":[[0,0],[0,0],[-3.609,0.001],[0,0],[0.373,0.014],[0,0],[14.167,-0.002]],"v":[[89.515,99.81],[106.415,-124.885],[-99.958,-124.851],[-106.142,-118.18],[-87.786,124.858],[-86.664,124.884],[62.514,124.861]],"c":true}]}],"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[182.699,202.107],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":1,"k":[{"i":{"x":0.782,"y":1},"o":{"x":0.861,"y":0},"t":10,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[119.595,-138.497],[-119.62,-138.459],[-120.576,-138.377],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.576,-138.411]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":25,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[119.124,-129.509],[-119.489,-140.956],[-120.445,-140.874],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.105,-129.423]],"c":true}]},{"i":{"x":0.491,"y":1},"o":{"x":0.527,"y":0},"t":35,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[119.418,-159.516],[-119.348,-117.118],[-120.304,-117.036],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.399,-159.43]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":45,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[118.011,-121.587],[-121.432,-155.871],[-122.388,-155.789],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[118.992,-121.501]],"c":true}]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":55,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[118.855,-144.345],[-120.181,-132.619],[-121.137,-132.537],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[119.836,-144.259]],"c":true}]},{"i":{"x":0.764,"y":0.716},"o":{"x":0.478,"y":0},"t":65,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[118.348,-130.69],[-120.932,-146.57],[-121.888,-146.488],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[119.329,-130.604]],"c":true}]},{"i":{"x":0.442,"y":1},"o":{"x":0.272,"y":0.981},"t":75,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[119.242,-141.512],[-119.433,-131.421],[-120.389,-131.339],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.223,-141.426]],"c":true}]},{"t":90,"s":[{"i":[[0.335,0],[0,0],[0.313,-0.048],[0,0],[-14.167,0.002],[0,0],[-1.062,14.128],[0,0]],"o":[[0,0],[-0.326,0],[0,0],[1.066,14.127],[0,0],[14.167,-0.002],[0,0],[-0.32,-0.051]],"v":[[119.595,-138.497],[-119.62,-138.459],[-120.576,-138.377],[-101.553,113.453],[-74.545,138.495],[74.633,138.472],[101.634,113.421],[120.576,-138.411]],"c":true}]}],"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[170.579,188.497],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":6,"ty":4,"nm":"Glass 2","parent":7,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":10,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":25,"s":[-3]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":35,"s":[10]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":45,"s":[-8]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":55,"s":[5]},{"i":{"x":[0.764],"y":[0.887]},"o":{"x":[0.478],"y":[0]},"t":65,"s":[-3]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.588]},"t":75,"s":[1.5]},{"t":90,"s":[0]}],"ix":10},"p":{"a":0,"k":[325.694,47.039,0],"ix":2},"a":{"a":0,"k":[176.077,402.77,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[14.167,-0.002],[0,0],[1.067,14.127],[0,0],[-3.397,0],[0,0],[0.254,-3.388],[0,0]],"o":[[0,0],[-14.167,0.002],[0,0],[-0.256,-3.387],[0,0],[3.397,-0.001],[0,0],[-1.063,14.127]],"v":[[74.645,176.36],[-74.533,176.383],[-101.542,151.342],[-125.82,-170.068],[-119.999,-176.346],[119.998,-176.384],[125.823,-170.107],[101.646,151.31]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[176.076,226.385],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[-0.271,-3.6],[0,0],[-2.362,0],[0,0],[-1.226,16.293],[0,0]],"o":[[-3.61,0],[0,0],[2.218,0.499],[0,0],[16.34,-0.003],[0,0],[0,0]],"v":[[-106.596,-162.739],[-112.782,-156.068],[-88.756,162.004],[-81.874,162.774],[59.6,162.751],[90.742,133.86],[113.053,-162.774]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[0.62400004069,0.991999966491,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[187.269,239.996],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.609,-0.001],[0,0],[-0.272,-3.6],[0,0],[-16.339,0.002],[0,0],[-1.225,16.293],[0,0]],"o":[[0,0],[-3.61,0],[0,0],[1.231,16.293],[0,0],[16.34,-0.003],[0,0],[0.27,-3.6]],"v":[[119.605,-176.385],[-119.605,-176.347],[-125.79,-169.676],[-101.833,147.502],[-70.683,176.384],[70.792,176.361],[101.934,147.469],[125.792,-169.716]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,1,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[176.076,226.386],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":7,"ty":3,"nm":"Position Controller 4","sr":1,"ks":{"o":{"a":0,"k":0,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":4,"s":[445.607,889.989,0],"to":[0,0,0],"ti":[0,0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":56,"s":[445.607,809.989,0],"to":[0,0,0],"ti":[0,0,0]},{"t":100,"s":[445.607,889.989,0]}],"ix":2},"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"ip":0,"op":100,"st":-2,"bm":0},{"ddd":0,"ind":8,"ty":4,"nm":"Fork & Spoon","parent":10,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[329.037,518.365,0],"ix":2},"a":{"a":0,"k":[208.366,208.366,0],"ix":1},"s":{"a":1,"k":[{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":10,"s":[80,80,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.166,-0.166,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":15,"s":[70,70,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-1.866,-1.866,0]},"t":20,"s":[90,90,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":24,"s":[80,80,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":59.75,"s":[80,80,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":64.75,"s":[70,70,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-2.099,-2.099,0]},"t":70,"s":[90,90,100]},{"t":74.5,"s":[80,80,100]}],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-18.88],[16.378,0],[0,18.88],[-16.379,0]],"o":[[0,18.88],[-16.379,0],[0,-18.88],[16.378,0]],"v":[[29.656,0],[0,34.186],[-29.656,0],[0,-34.186]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[260.161,175.206],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[11.435,-5.217],[0,0]],"o":[[0,0],[0,11.179],[0,0],[0,0]],"v":[[14.828,-35.101],[14.828,3.393],[-3.763,30.051],[-14.828,35.101]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[175.079,176.121],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[-11.435,-5.217],[0,0]],"o":[[0,0],[0,11.179],[0,0],[0,0]],"v":[[-14.827,-35.101],[-14.827,3.393],[3.762,30.051],[14.827,35.101]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[145.424,176.121],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[260.162,209.391],[260.162,297.296]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[0,0],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[160.252,141.02],[160.252,297.296]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[0,0],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":2,"cix":2,"bm":0,"ix":5,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":9,"ty":4,"nm":"Label 2","parent":10,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[329.037,518.365,0],"ix":2},"a":{"a":0,"k":[208.366,208.366,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,-87.463],[87.464,0],[0,87.464],[-87.463,0]],"o":[[0,87.464],[-87.463,0],[0,-87.463],[87.464,0]],"v":[[158.366,0],[0,158.366],[-158.366,0],[0,-158.366]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[208.366,208.366],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 6","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,87.464],[34.098,29.047],[20.423,0],[0,-87.464],[-34.099,-29.048],[-20.423,0]],"o":[[0,-48.305],[-17.926,-7.04],[-87.464,0],[0,48.305],[17.925,7.039],[87.464,0]],"v":[[135.982,-13.43],[80.251,-134.027],[22.384,-144.936],[-135.982,13.431],[-80.25,134.028],[-22.384,144.936]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.686274509804,0.109803929048,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[230.75,221.796],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 7","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[87.463,0],[0,-87.463],[-87.463,0],[0,87.464]],"o":[[-87.463,0],[0,87.464],[87.463,0],[0,-87.463]],"v":[[0,-158.366],[-158.366,0],[0,158.366],[158.366,0]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.831372608858,0.521568627451,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[208.366,208.366],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 8","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":10,"ty":4,"nm":"Bag ","parent":11,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[47.077,-626.274,0],"ix":2},"a":{"a":0,"k":[329.943,50,0],"ix":1},"s":{"a":1,"k":[{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":0,"s":[104,97,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":50,"s":[100,100,100]},{"t":100,"s":[104,97,100]}],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[51.62,0],[0,-51.619],[0,0]],"o":[[0,0],[0,-51.619],[-51.621,0],[0,0],[0,0]],"v":[[93.466,99.309],[93.466,-5.843],[0.001,-99.309],[-93.467,-5.843],[-93.467,99.309]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[326.047,149.308],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[16.114,0],[0,0],[-1.256,16.065],[0,0],[-14.431,0],[0,0],[-1.124,-14.387],[0,0]],"o":[[0,0],[-16.114,0],[0,0],[1.124,-14.387],[0,0],[14.431,0],[0,0],[1.255,16.065]],"v":[[251.131,294.836],[-251.131,294.836],[-278.687,265.042],[-236.938,-269.347],[-209.381,-294.836],[209.381,-294.836],[236.939,-269.347],[278.688,265.042]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[329.943,492.376],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[1.286,16.486],[0,0],[0,0],[1.153,-14.764],[0,0]],"o":[[16.522,0],[0,0],[0,0],[-14.797,0],[0,0],[0,0]],"v":[[219.855,267.105],[248.111,236.531],[208.796,-267.105],[-181.482,-267.105],[-209.738,-240.949],[-249.397,267.105]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[352.518,522.106],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[1.255,16.065],[0,0],[14.431,0],[0,0],[1.124,-14.386],[0,0],[-16.115,0],[0,0]],"o":[[0,0],[-1.124,-14.386],[0,0],[-14.431,0],[0,0],[-1.255,16.065],[0,0],[16.115,0]],"v":[[278.688,265.041],[236.939,-269.348],[209.381,-294.835],[-209.381,-294.835],[-236.938,-269.348],[-278.687,265.041],[-251.13,294.835],[251.131,294.835]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[329.943,492.376],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":11,"ty":3,"nm":"Position Controller 2","sr":1,"ks":{"o":{"a":0,"k":0,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[437.607,835.989,0],"to":[0,0,0],"ti":[0,0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[437.607,795.989,0],"to":[0,0,0],"ti":[0,0,0]},{"t":100,"s":[437.607,835.989,0]}],"ix":2},"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"ip":0,"op":100,"st":-2,"bm":0}],"markers":[]}';
let honeymoonTravellingLottie = '{"v":"5.5.7","meta":{"g":"LottieFiles AE 0.1.20","a":"","k":"","d":"","tc":""},"fr":25,"ip":0,"op":100,"w":1000,"h":1000,"nm":"Love_29_Case","ddd":0,"assets":[],"layers":[{"ddd":0,"ind":1,"ty":4,"nm":"Heart Big ","parent":4,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[417.598,487.904,0],"ix":2},"a":{"a":0,"k":[155.67,138.021,0],"ix":1},"s":{"a":1,"k":[{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":4,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":9,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-1.866,-1.866,0]},"t":14.25,"s":[110,110,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":18.25,"s":[100,100,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":62.25,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":67.25,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-2.332,-2.332,0]},"t":72.5,"s":[110,110,100]},{"t":77.5,"s":[100,100,100]}],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[21.04,6.005],[0,0],[21.206,13.375],[17.071,-38.191],[0,0],[-23.765,53.165]],"o":[[-24.109,-6.88],[0,0],[-18.507,-11.673],[-23.765,53.165],[0,0],[17.071,-38.191]],"v":[[55.421,-43.892],[13.527,-34.504],[-7.419,-71.981],[-81.905,-49.83],[-41.241,88.021],[88.599,26.384]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[155.67,138.021],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[-17.221,-29.213],[-19.79,44.273],[13.567,12.344],[0.022,0.007],[15.33,3.173],[0,0],[2.536,7.627],[15.515,-34.708]],"o":[[25.159,-3.203],[11.351,-25.396],[-0.021,-0.006],[-18.009,-5.139],[-13.813,2.3],[0,0],[-21.877,-2.997],[-15.568,34.83]],"v":[[-46.828,73.552],[74.979,12.798],[63.65,-44.98],[63.586,-45],[22.68,-58.573],[-0.092,-48.091],[-2.566,-61.669],[-70.763,-38.844]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[169.29,151.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[21.04,6.005],[0,0],[21.206,13.375],[17.071,-38.191],[0,0],[-23.765,53.165]],"o":[[-24.109,-6.88],[0,0],[-18.507,-11.673],[-23.765,53.165],[0,0],[17.071,-38.191]],"v":[[55.421,-43.892],[13.527,-34.504],[-7.419,-71.981],[-81.905,-49.83],[-41.241,88.021],[88.599,26.384]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[155.67,138.021],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":2,"ty":4,"nm":"Heart Left ","parent":4,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[176.075,331.682,0],"ix":2},"a":{"a":0,"k":[124.505,115.018,0],"ix":1},"s":{"a":1,"k":[{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":0,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":5,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-1.866,-1.866,0]},"t":10.25,"s":[110,110,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":14.25,"s":[100,100,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":58.25,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":63.25,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-2.332,-2.332,0]},"t":68.5,"s":[110,110,100]},{"t":73.5,"s":[100,100,100]}],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[17.281,-2.477],[0,0],[19.801,2.838],[0,-33.377],[0,0],[0,46.463]],"o":[[-19.801,2.838],[0,0],[-17.281,-2.477],[0,46.463],[0,0],[0,-33.377]],"v":[[27.457,-62.541],[-0.002,-42.062],[-27.461,-62.541],[-74.505,-22.153],[-0.002,65.018],[74.505,-22.153]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[124.505,115.018],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[-22.055,-15.672],[0,38.693],[13.901,4.574],[0.017,-0.003],[12.2,-2.68],[0,0],[4.331,4.73],[0,-30.333]],"o":[[17.283,-10.525],[0,-22.194],[-0.017,0.002],[-14.792,2.119],[-9.313,6.173],[0,0],[-16.91,4.94],[0,30.438]],"v":[[-7.457,61.155],[61.486,-22.759],[34.422,-61.155],[34.37,-61.148],[0.154,-57.717],[-13.02,-42.667],[-19.244,-51.752],[-61.485,-12.922]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[137.523,115.622],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[17.281,-2.477],[0,0],[19.801,2.838],[0,-33.377],[0,0],[0,46.463]],"o":[[-19.801,2.838],[0,0],[-17.281,-2.477],[0,46.463],[0,0],[0,-33.377]],"v":[[27.458,-62.541],[-0.001,-42.062],[-27.46,-62.541],[-74.505,-22.153],[-0.001,65.018],[74.505,-22.153]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[124.505,115.018],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":3,"ty":4,"nm":"Heart Right ","parent":4,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[636.075,331.682,0],"ix":2},"a":{"a":0,"k":[124.505,115.018,0],"ix":1},"s":{"a":1,"k":[{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":8,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":13,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-1.866,-1.866,0]},"t":18.25,"s":[110,110,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":22.25,"s":[100,100,100]},{"i":{"x":[0.833,0.833,0.833],"y":[1,1,1]},"o":{"x":[0.167,0.167,0.167],"y":[0,0,0]},"t":66.25,"s":[100,100,100]},{"i":{"x":[0.667,0.667,0.667],"y":[-0.224,-0.224,1]},"o":{"x":[0.333,0.333,0.333],"y":[0,0,0]},"t":71.25,"s":[90,90,100]},{"i":{"x":[0.667,0.667,0.667],"y":[1,1,1]},"o":{"x":[0.333,0.333,0.333],"y":[-2.332,-2.332,0]},"t":76.5,"s":[110,110,100]},{"t":81.5,"s":[100,100,100]}],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[17.28,-2.477],[0,0],[19.802,2.838],[0,-33.377],[0,0],[0,46.463]],"o":[[-19.802,2.838],[0,0],[-17.28,-2.477],[0,46.463],[0,0],[0,-33.377]],"v":[[27.457,-62.541],[-0.002,-42.062],[-27.462,-62.541],[-74.505,-22.153],[-0.002,65.018],[74.505,-22.153]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[124.505,115.018],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[-22.056,-15.672],[0,38.693],[13.901,4.574],[0.018,-0.003],[12.201,-2.68],[0,0],[4.331,4.73],[0,-30.333]],"o":[[17.282,-10.525],[0,-22.194],[-0.018,0.002],[-14.791,2.119],[-9.312,6.173],[0,0],[-16.911,4.94],[0,30.438]],"v":[[-7.457,61.155],[61.486,-22.759],[34.421,-61.155],[34.368,-61.148],[0.152,-57.717],[-13.021,-42.667],[-19.245,-51.752],[-61.486,-12.922]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[137.524,115.622],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[17.28,-2.477],[0,0],[19.802,2.838],[0,-33.377],[0,0],[0,46.463]],"o":[[-19.802,2.838],[0,0],[-17.28,-2.477],[0,46.463],[0,0],[0,-33.377]],"v":[[27.457,-62.541],[-0.002,-42.062],[-27.462,-62.541],[-74.505,-22.153],[-0.002,65.018],[74.505,-22.153]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[124.505,115.018],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":4,"ty":4,"nm":"Case ","parent":5,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":10,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":25,"s":[-1]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":35,"s":[4]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":45,"s":[-3]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":55,"s":[2]},{"i":{"x":[0.764],"y":[0.796]},"o":{"x":[0.478],"y":[0]},"t":65,"s":[-1.5]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.883]},"t":75,"s":[1]},{"t":90,"s":[0]}],"ix":10},"p":{"a":0,"k":[48.755,30.385,0],"ix":2},"a":{"a":0,"k":[405,684.585,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[34.5,-251.978],[-34.5,-251.978],[-34.5,251.978],[34.5,251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[637.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-17.5,251.978],[17.5,251.978],[17.5,-251.978],[-17.5,-251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[0.62400004069,0.991999966491,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[654.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-34.5,251.978],[34.5,251.978],[34.5,-251.978],[-34.5,-251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,1,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[637.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[34.5,-251.978],[-34.5,-251.978],[-34.5,251.978],[34.5,251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[175.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-17.5,251.978],[17.5,251.978],[17.5,-251.978],[-17.5,-251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[0.62400004069,0.991999966491,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[192.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":2,"cix":2,"bm":0,"ix":5,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-34.5,251.978],[34.5,251.978],[34.5,-251.978],[-34.5,-251.978]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,1,1,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[175.171,432.607],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 6","np":2,"cix":2,"bm":0,"ix":6,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[19.33,0],[0,0],[0,19.33],[0,0],[-19.33,0],[0,0],[0,-19.33],[0,0]],"o":[[0,0],[-19.33,0],[0,0],[0,-19.33],[0,0],[19.33,0],[0,0],[0,19.33]],"v":[[320,252.5],[-320,252.5],[-355,217.5],[-355,-217.5],[-320,-252.5],[320,-252.5],[355,-217.5],[355,217.5]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[405,432.085],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 7","np":2,"cix":2,"bm":0,"ix":7,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,-19.33],[0,0],[0,0],[0,19.33],[0,0]],"o":[[-19.33,0],[0,0],[0,0],[19.33,0],[0,0],[0,0]],"v":[[-300.5,-232.5],[-335.5,-197.5],[-335.5,232.5],[300.5,232.5],[335.5,197.5],[335.5,-232.5]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[424.5,452.085],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 8","np":2,"cix":2,"bm":0,"ix":8,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[19.33,0],[0,0],[0,-19.33],[0,0],[-19.33,0],[0,0],[0,19.33],[0,0]],"o":[[0,0],[-19.33,0],[0,0],[0,19.33],[0,0],[19.33,0],[0,0],[0,-19.33]],"v":[[320,-252.5],[-320,-252.5],[-355,-217.5],[-355,217.5],[-320,252.5],[320,252.5],[355,217.5],[355,-217.5]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[405,432.085],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 9","np":2,"cix":2,"bm":0,"ix":9,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[31.977,0],[0,0],[0,-31.977],[0,0],[0,0],[0,0],[-8.028,0],[0,0],[0,-7.968],[0,0],[0,0],[0,0]],"o":[[0,0],[-31.977,0],[0,0],[0,0],[0,0],[0,-7.968],[0,0],[8.027,0],[0,0],[0,0],[0,0],[0,-31.977]],"v":[[79.547,-64.815],[-79.546,-64.815],[-137.397,-6.962],[-137.397,64.815],[-92.423,64.815],[-92.423,-2.5],[-77.96,-16.962],[77.961,-16.962],[92.424,-2.5],[92.424,64.815],[137.397,64.815],[137.397,-6.962]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[405,114.815],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 10","np":2,"cix":2,"bm":0,"ix":10,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[17.696,0],[0,0],[0,-17.696],[0,0],[0,0],[0,0],[-8.027,0],[0,0],[-2.545,-2.25],[0,0],[0,-4.41],[0,0],[0,0],[0,0]],"o":[[0,0],[-17.696,0],[0,0],[0,0],[0,0],[0,-7.968],[0,0],[3.684,0],[0,0],[4.442,0],[0,0],[0,0],[0,0],[0,-17.696]],"v":[[87.019,-48.368],[-88.02,-48.368],[-120.034,-16.353],[-120.034,48.368],[-100.061,48.368],[-100.061,-11.053],[-85.598,-25.515],[70.324,-25.515],[79.891,-21.887],[87.142,-21.887],[95.146,-13.884],[95.146,48.368],[120.034,48.368],[120.034,-16.353]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[412.637,123.368],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 11","np":2,"cix":2,"bm":0,"ix":11,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[31.977,0],[0,0],[0,-31.977],[0,0],[0,0],[0,0],[-8.028,0],[0,0],[0,-7.968],[0,0],[0,0],[0,0]],"o":[[0,0],[-31.977,0],[0,0],[0,0],[0,0],[0,-7.968],[0,0],[8.027,0],[0,0],[0,0],[0,0],[0,-31.977]],"v":[[79.547,-64.815],[-79.546,-64.815],[-137.397,-6.962],[-137.397,64.815],[-92.423,64.815],[-92.423,-2.5],[-77.96,-16.962],[77.961,-16.962],[92.424,-2.5],[92.424,64.815],[137.397,64.815],[137.397,-6.962]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[405,114.815],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 12","np":2,"cix":2,"bm":0,"ix":12,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":5,"ty":3,"nm":"Position Controller 2","sr":1,"ks":{"o":{"a":0,"k":0,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[505.607,835.989,0],"to":[0,0,0],"ti":[0,0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":50,"s":[505.607,815.989,0],"to":[0,0,0],"ti":[0,0,0]},{"t":100,"s":[505.607,835.989,0]}],"ix":2},"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"ip":0,"op":100,"st":-2,"bm":0}],"markers":[]}';
let flyingPigLottie = '{"nm":"Pig","ddd":0,"h":350,"w":1668,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":4,"nm":"Kaki 2","sr":1,"st":-5,"op":82,"ip":-5,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-299.53,39,0],"ix":1},"s":{"a":0,"k":[23.31,23.31,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[10.096,11.845,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[-10],"t":-5},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":-4},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":-3},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":-2},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":-1},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":0},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":1},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":2},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":3},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":4},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":5},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":6},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":7},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":8},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":9},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":10},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":11},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":12},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":13},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":14},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":15},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":16},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":17},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":18},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":19},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":20},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":21},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":22},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":23},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":24},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":25},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":26},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":27},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":28},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":29},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":30},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":31},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":32},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":33},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":34},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":35},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":36},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":37},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":38},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":39},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":40},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":41},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":42},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":43},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":44},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":45},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":46},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":47},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":48},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":49},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":50},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":51},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":52},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":53},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":54},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":55},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":56},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":57},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":58},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":59},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":60},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":61},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":62},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":63},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":64},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":65},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":66},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":67},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":68},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":69},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":70},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":71},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":72},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":73},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":74},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":75},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":76},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":77},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":78},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":79},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.833},"s":[0],"t":80},{"s":[-1.04],"t":81}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]},"ix":2}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":100,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":90,"ix":1},"m":1},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-282.913,118.405]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[1,0.4824,0.6745],"ix":3}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":3,"e":{"a":0,"k":88.5,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1,"parent":7},{"ty":4,"nm":"Kaki 3","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-299.53,39,0],"ix":1},"s":{"a":0,"k":[23.31,23.31,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[-17.876,11.845,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[-10],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[0],"t":5},{"s":[-10],"t":10}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":1},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":2},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":3},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":4},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":5},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":6},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":7},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":8},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":9},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":10},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":11},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":12},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":13},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":14},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":16},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":17},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":18},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":19},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":20},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":21},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":22},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":23},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":24},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":25},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":26},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":27},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":28},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":29},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":30},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":31},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":32},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":33},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":34},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":35},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":36},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":37},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":38},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":39},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":40},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":41},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":42},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":43},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":44},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":45},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":46},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":47},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":48},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":49},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":50},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":51},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":52},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":53},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":54},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":55},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":56},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":57},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":58},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":59},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":60},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":61},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":62},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":63},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":64},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":65},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":66},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":67},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":68},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":69},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":70},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":71},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":72},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":73},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":74},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":75},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":76},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":77},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":78},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":79},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":80},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":81},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":82},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":83},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":84},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":85},{"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":86}],"ix":2}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":100,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":90,"ix":1},"m":1},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-282.913,118.405]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[1,0.4824,0.6745],"ix":3}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":3,"e":{"a":0,"k":88.5,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2,"parent":7},{"ty":3,"nm":"Null 6","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[429,429,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[581.476,137.177,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":3},{"ty":4,"nm":"Layer 5","sr":1,"st":-2,"op":85,"ip":-2,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-6.061,3.03,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[674.75,-18.406,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[-10],"t":-2},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":-1},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":0},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":1},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":2},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":3},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":4},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":5},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":6},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":7},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":8},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":9},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":10},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":11},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":12},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":13},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":14},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":15},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":16},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":17},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":18},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":19},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":20},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":21},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":22},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":23},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":24},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":25},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":26},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":27},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":28},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":29},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":30},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":31},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":32},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":33},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":34},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":35},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":36},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":37},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":38},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":39},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":40},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":41},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":42},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":43},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":44},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":45},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":46},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":47},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":48},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":49},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":50},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":51},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":52},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":53},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":54},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":55},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":56},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":57},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":58},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":59},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":60},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":61},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":62},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":63},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":64},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":65},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":66},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":67},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":68},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":69},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":70},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":71},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":72},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":73},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":74},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":75},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":76},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":77},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":78},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":79},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":80},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":81},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":82},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.833},"s":[0],"t":83},{"s":[-1.04],"t":84}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[4.726,-1.836],[1.836,4.726],[-4.726,1.836],[-9.849,-2.222]],"o":[[-4.726,1.836],[-1.836,-4.726],[4.726,-1.836],[4.946,1.116]],"v":[[0.357,8.543],[-11.526,3.31],[-6.293,-8.573],[10.879,-5.395]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4,"parent":6},{"ty":4,"nm":"Layer 4","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.341,1.935,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[77.127,43.809,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":1},"s":[34.96],"t":0},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":1},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":2},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":3},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":4},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":5},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":6},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":7},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":8},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":9},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":10},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":11},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":12},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":13},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":14},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":15},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":16},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":17},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":18},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":19},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":20},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":21},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":22},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":23},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":24},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":25},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":26},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":27},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":28},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":29},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":30},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":31},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":32},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":33},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":34},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":35},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":36},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":37},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":38},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":39},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":40},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":41},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":42},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":43},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":44},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":45},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":46},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":47},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":48},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":49},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":50},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":51},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":52},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":53},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":54},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":55},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":56},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":57},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":58},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":59},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":60},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":61},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":62},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":63},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":64},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":65},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":66},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":67},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":68},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":69},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":70},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":71},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":72},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":73},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":74},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[27.04],"t":75},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[26],"t":76},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[27.04],"t":77},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[29.52],"t":78},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[32.48],"t":79},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[34.96],"t":80},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[36],"t":81},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[34.96],"t":82},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[32.48],"t":83},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[29.52],"t":84},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.833},"s":[27.04],"t":85},{"s":[26],"t":86}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[-2.093,1.506]],"o":[[2.347,-1.066],[0,0]],"v":[[-3.341,1.935],[3.341,-1.935]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":2,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":3,"ix":5},"c":{"a":0,"k":[1,0.4824,0.6745],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5,"parent":3},{"ty":4,"nm":"Kepala","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[680.682,6.773,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[33.206,67.596,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":0},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":1},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":2},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":3},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":4},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":5},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":6},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":7},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":8},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":9},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":10},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":11},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":12},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":13},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":14},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":15},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":16},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":17},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":18},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":19},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":20},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":21},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":22},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":23},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":24},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":25},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":26},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":27},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":28},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":29},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":30},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":31},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":32},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":33},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":34},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":35},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":36},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":37},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":38},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":39},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":40},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":41},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":42},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":43},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":44},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":45},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":46},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":47},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":48},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":49},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":50},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":51},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":52},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":53},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":54},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":55},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":56},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":57},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":58},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":59},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":60},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":61},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":62},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":63},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":64},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":65},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":66},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":67},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":68},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":69},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":70},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":71},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":72},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":73},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":74},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.731},"s":[0],"t":75},{"o":{"x":0.167,"y":0.121},"i":{"x":0.833,"y":0.811},"s":[0.354],"t":76},{"o":{"x":0.167,"y":0.149},"i":{"x":0.833,"y":0.83},"s":[1.146],"t":77},{"o":{"x":0.167,"y":0.163},"i":{"x":0.833,"y":0.86},"s":[2.146],"t":78},{"o":{"x":0.167,"y":0.206},"i":{"x":0.833,"y":0.964},"s":[3.191],"t":79},{"o":{"x":0.167,"y":-0.062},"i":{"x":0.833,"y":0.718},"s":[3.9],"t":80},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[3.494],"t":81},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[2.527],"t":82},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[1.373],"t":83},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":0.989},"s":[0.406],"t":84},{"o":{"x":0.167,"y":-0.012},"i":{"x":0.833,"y":0.833},"s":[0],"t":85},{"s":[0.354],"t":86}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[-1.51,1.51],[-1.51,-1.51]],"o":[[1.51,-1.51],[1.51,1.51]],"v":[[-2.734,0.566],[2.734,0.566]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":2,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":1,"ix":5},"c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[650.749,-9.797],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[-1.51,1.51],[-1.51,-1.51]],"o":[[1.51,-1.51],[1.51,1.51]],"v":[[-2.734,0.566],[2.734,0.566]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":2,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":1,"ix":5},"c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[662.85,-9.797],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":2,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,-0.934],[0.934,0],[0,0.934],[-0.934,0]],"o":[[0,0.934],[-0.934,0],[0,-0.934],[0.934,0]],"v":[[1.691,0],[0,1.691],[-1.691,0],[0,-1.691]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[654.816,0.272],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,-0.934],[0.934,0],[0,0.934],[-0.934,0]],"o":[[0,0.934],[-0.934,0],[0,-0.934],[0.934,0]],"v":[[1.691,0],[0,1.691],[-1.691,0],[0,-1.691]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[649.903,0.272],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[649.903,0.272],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[649.903,0.272],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[2.847,0],[0,0],[0,2.847],[0,0],[-2.847,0],[0,0],[0,-2.847],[0,0]],"o":[[0,0],[-2.847,0],[0,0],[0,-2.847],[0,0],[2.847,0],[0,0],[0,2.847]],"v":[[3.221,5.154],[-3.221,5.154],[-8.376,0],[-8.376,0],[-3.221,-5.154],[3.221,-5.154],[8.376,0],[8.376,0]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9765,0.3451,0.6],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[652.36,0.272],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[652.36,0.272],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[652.36,0.272],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,-11.722],[11.722,0],[0,11.722],[-11.722,0]],"o":[[0,11.722],[-11.722,0],[0,-11.722],[11.722,0]],"v":[[21.225,0],[0,21.225],[-21.225,0],[0,-21.225]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[669.582,-4.882],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6,"parent":3},{"ty":4,"nm":"Body","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[52.098,60.613,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[11.884,0],[0,0],[0,11.884],[0,0],[-11.884,0],[0,0],[0,-11.884],[0,0]],"o":[[0,0],[-11.884,0],[0,0],[0,-11.884],[0,0],[11.884,0],[0,0],[0,11.884]],"v":[[13.274,21.518],[-13.274,21.518],[-34.792,0],[-34.792,0],[-13.274,-21.518],[13.274,-21.518],[34.792,0],[34.792,0]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":7,"parent":3},{"ty":4,"nm":"Layer 1","sr":1,"st":-2,"op":85,"ip":-2,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-6.993,2.797,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[661.666,-16.703,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[-10],"t":-2},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":-1},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":0},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":1},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":2},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":3},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":4},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":5},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":6},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":7},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":8},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":9},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":10},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":11},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":12},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":13},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":14},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":15},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":16},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":17},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":18},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":19},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":20},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":21},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":22},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":23},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":24},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":25},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":26},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":27},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":28},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":29},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":30},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":31},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":32},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":33},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":34},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":35},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":36},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":37},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":38},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":39},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":40},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":41},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":42},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":43},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":44},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":45},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":46},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":47},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":48},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":49},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":50},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":51},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":52},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":53},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":54},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":55},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":56},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":57},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":58},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":59},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":60},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":61},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":62},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":63},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":64},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":65},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":66},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":67},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":68},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":69},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":70},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":71},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":72},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":73},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":74},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":75},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":76},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":77},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":78},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":79},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":80},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":81},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":82},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.833},"s":[0],"t":83},{"s":[-1.04],"t":84}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[4.726,-1.836],[1.836,4.726],[-4.726,1.836],[-9.849,-2.222]],"o":[[-4.726,1.836],[-1.836,-4.726],[4.726,-1.836],[4.946,1.116]],"v":[[0.357,8.543],[-11.526,3.31],[-6.293,-8.573],[10.879,-5.395]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9294,0.4196,0.6275],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":8,"parent":6},{"ty":0,"nm":"Asap 2","sr":1,"st":0,"op":180,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[634.5,130.5,0],"ix":1},"s":{"a":0,"k":[23.31,23.31,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[205.387,59.728,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":1269,"h":261,"refId":"comp_0","ind":9,"parent":3},{"ty":4,"nm":"Kaki","sr":1,"st":-3,"op":84,"ip":-3,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-299.53,39,0],"ix":1},"s":{"a":0,"k":[23.31,23.31,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[-23.237,10.213,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[-10],"t":-3},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":-2},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":-1},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":0},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":1},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":2},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":3},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":4},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":5},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":6},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":7},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":8},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":9},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":10},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":11},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":12},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":13},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":14},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":15},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":16},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":17},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":18},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":19},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":20},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":21},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":22},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":23},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":24},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":25},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":26},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":27},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":28},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":29},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":30},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":31},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":32},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":33},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":34},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":35},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":36},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":37},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":38},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":39},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":40},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":41},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":42},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":43},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":44},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":45},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":46},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":47},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":48},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":49},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":50},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":51},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":52},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":53},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":54},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":55},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":56},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":57},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":58},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":59},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":60},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":61},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":62},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":63},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":64},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":65},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":66},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":67},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":68},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":69},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":70},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":71},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":72},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":73},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":74},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":75},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":76},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":77},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":78},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":79},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":80},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":81},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.833},"s":[0],"t":82},{"s":[-1.04],"t":83}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":-3},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":-2},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":-1},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":1},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":2},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":3},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":4},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":5},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":6},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":7},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":8},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":9},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":10},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":11},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":12},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":13},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":14},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":16},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":17},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":18},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":19},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":20},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":21},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":22},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":23},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":24},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":25},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":26},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":27},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":28},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":29},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":30},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":31},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":32},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":33},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":34},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":35},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":36},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":37},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":38},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":39},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":40},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":41},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":42},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":43},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":44},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":45},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":46},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":47},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":48},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":49},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":50},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":51},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":52},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":53},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":54},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":55},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":56},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":57},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":58},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":59},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":60},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":61},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":62},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":63},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":64},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":65},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":66},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":67},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":68},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":69},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":70},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":71},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":72},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":73},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":74},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":75},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":76},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]}],"t":77},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.978,-5.075]],"o":[[-1,37],[16.613,4.763]],"v":[[-308,45],[-262.517,97.585]]}],"t":78},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.925,-7.638]],"o":[[-1,37],[15.691,6.584]],"v":[[-308,45],[-268.163,103.347]]}],"t":79},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.862,-10.697]],"o":[[-1,37],[14.59,8.757]],"v":[[-308,45],[-274.901,110.225]]}],"t":80},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":81},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[1.51,-55.881],[-16.787,-14.335]],"o":[[-1,37],[13.281,11.341]],"v":[[-308,45],[-282.913,118.405]]}],"t":82},{"s":[{"c":false,"i":[[1.51,-55.881],[-16.809,-13.26]],"o":[[-1,37],[13.668,10.577]],"v":[[-308,45],[-280.546,115.988]]}],"t":83}],"ix":2}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":100,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":90,"ix":1},"m":1},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[0.9294,0.2157,0.5412],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-282.913,118.405]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[0.9922,0.4,0.6196],"ix":3}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":3,"e":{"a":0,"k":88.5,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":10,"parent":7},{"ty":4,"nm":"Kaki 4","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-299.53,39,0],"ix":1},"s":{"a":0,"k":[23.31,23.31,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[6.6,11.845,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.718},"s":[-10],"t":0},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":1},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":2},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":3},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":4},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":5},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":6},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":7},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":8},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":9},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":10},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":11},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":12},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":13},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":14},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":15},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":16},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":17},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":18},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":19},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":20},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":21},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":22},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":23},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":24},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":25},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":26},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":27},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":28},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":29},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":30},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":31},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":32},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":33},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":34},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":35},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":36},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":37},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":38},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":39},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":40},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":41},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":42},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":43},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":44},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":45},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":46},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":47},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":48},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":49},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":50},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":51},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":52},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":53},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":54},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":55},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":56},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":57},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":58},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":59},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":60},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":61},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":62},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":63},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":64},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":65},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":66},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":67},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":68},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":69},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":70},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":71},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":72},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":73},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":74},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[0],"t":75},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-1.04],"t":76},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-3.52],"t":77},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-6.48],"t":78},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-8.96],"t":79},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.718},"s":[-10],"t":80},{"o":{"x":0.167,"y":0.118},"i":{"x":0.833,"y":0.817},"s":[-8.96],"t":81},{"o":{"x":0.167,"y":0.153},"i":{"x":0.833,"y":0.847},"s":[-6.48],"t":82},{"o":{"x":0.167,"y":0.183},"i":{"x":0.833,"y":0.882},"s":[-3.52],"t":83},{"o":{"x":0.167,"y":0.282},"i":{"x":0.833,"y":1},"s":[-1.04],"t":84},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":0.833},"s":[0],"t":85},{"s":[-1.04],"t":86}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-260.15,95.168]]},"ix":2}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":100,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":90,"ix":1},"m":1},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":4,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[1.51,-55.881],[-17,-4]],"o":[[-1,37],[17,4]],"v":[[-308,45],[-282.913,118.405]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":28,"ix":5},"c":{"a":0,"k":[0.9922,0.4,0.6196],"ix":3}},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":3,"e":{"a":0,"k":88.5,"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[9.562,-6.387],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":11,"parent":7},{"ty":4,"nm":"Shape Layer 3","sr":1,"st":0,"op":87,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[117,135.728,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[834,175,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[1668,300],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,99.673],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0.521,0.127],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":12}],"v":"5.7.12","fr":30,"op":60,"ip":0,"assets":[{"nm":"Asap 2","id":"comp_0","layers":[{"ty":4,"nm":"Shape Layer 36","sr":1,"st":165,"op":180,"ip":165,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":165},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":172.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":180}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"Shape Layer 35","sr":1,"st":165,"op":180,"ip":165,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":165},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":172.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":180}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"Shape Layer 34","sr":1,"st":165,"op":180,"ip":165,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":165},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":172.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":180}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"Shape Layer 33","sr":1,"st":150,"op":165,"ip":150,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":150},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":157.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":165}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4},{"ty":4,"nm":"Shape Layer 32","sr":1,"st":150,"op":165,"ip":150,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":150},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":157.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":165}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5},{"ty":4,"nm":"Shape Layer 31","sr":1,"st":150,"op":165,"ip":150,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":150},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":157.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":165}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6},{"ty":4,"nm":"Shape Layer 30","sr":1,"st":135,"op":150,"ip":135,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":135},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":142.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":150}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":7},{"ty":4,"nm":"Shape Layer 29","sr":1,"st":135,"op":150,"ip":135,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":135},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":142.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":150}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":8},{"ty":4,"nm":"Shape Layer 28","sr":1,"st":135,"op":150,"ip":135,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":135},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":142.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":150}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":9},{"ty":4,"nm":"Shape Layer 27","sr":1,"st":120,"op":135,"ip":120,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":120},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":127.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":135}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":10},{"ty":4,"nm":"Shape Layer 26","sr":1,"st":120,"op":135,"ip":120,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":120},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":127.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":135}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":11},{"ty":4,"nm":"Shape Layer 25","sr":1,"st":120,"op":135,"ip":120,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":120},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":127.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":135}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":12},{"ty":4,"nm":"Shape Layer 24","sr":1,"st":105,"op":120,"ip":105,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":105},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":112.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":120}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":13},{"ty":4,"nm":"Shape Layer 23","sr":1,"st":105,"op":120,"ip":105,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":105},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":112.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":120}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":14},{"ty":4,"nm":"Shape Layer 22","sr":1,"st":105,"op":120,"ip":105,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":105},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":112.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":120}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":15},{"ty":4,"nm":"Shape Layer 21","sr":1,"st":90,"op":105,"ip":90,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":90},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":97.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":105}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":16},{"ty":4,"nm":"Shape Layer 20","sr":1,"st":90,"op":105,"ip":90,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":90},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":97.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":105}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":17},{"ty":4,"nm":"Shape Layer 19","sr":1,"st":90,"op":105,"ip":90,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":90},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":97.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":105}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":18},{"ty":4,"nm":"Shape Layer 18","sr":1,"st":75,"op":90,"ip":75,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":75},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":82.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":90}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":19},{"ty":4,"nm":"Shape Layer 17","sr":1,"st":75,"op":90,"ip":75,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":75},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":82.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":90}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":20},{"ty":4,"nm":"Shape Layer 16","sr":1,"st":75,"op":90,"ip":75,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":75},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":82.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":90}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":21},{"ty":4,"nm":"Shape Layer 15","sr":1,"st":60,"op":75,"ip":60,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":60},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":67.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":75}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":22},{"ty":4,"nm":"Shape Layer 14","sr":1,"st":60,"op":75,"ip":60,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":60},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":67.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":75}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":23},{"ty":4,"nm":"Shape Layer 13","sr":1,"st":60,"op":75,"ip":60,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":60},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":67.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":75}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":24},{"ty":4,"nm":"Shape Layer 12","sr":1,"st":45,"op":60,"ip":45,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":45},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":52.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":60}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":25},{"ty":4,"nm":"Shape Layer 11","sr":1,"st":45,"op":60,"ip":45,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":45},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":52.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":60}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":26},{"ty":4,"nm":"Shape Layer 10","sr":1,"st":45,"op":60,"ip":45,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":45},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":52.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":60}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":27},{"ty":4,"nm":"Shape Layer 9","sr":1,"st":30,"op":45,"ip":30,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":30},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":37.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":45}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":28},{"ty":4,"nm":"Shape Layer 8","sr":1,"st":30,"op":45,"ip":30,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":30},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":37.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":45}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":29},{"ty":4,"nm":"Shape Layer 7","sr":1,"st":30,"op":45,"ip":30,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":30},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":37.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":45}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":30},{"ty":4,"nm":"Shape Layer 6","sr":1,"st":15,"op":30,"ip":15,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":22.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":30}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":31},{"ty":4,"nm":"Shape Layer 5","sr":1,"st":15,"op":30,"ip":15,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":22.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":30}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":32},{"ty":4,"nm":"Shape Layer 4","sr":1,"st":15,"op":30,"ip":15,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":22.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":30}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":33},{"ty":4,"nm":"Shape Layer 3","sr":1,"st":0,"op":15,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,175.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":7.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":15}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9843,0.0784,0.4157],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":34},{"ty":4,"nm":"Shape Layer 2","sr":1,"st":0,"op":15,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,131.134,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":7.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":15}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9961,0.349,0.5882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":35},{"ty":4,"nm":"Shape Layer 1","sr":1,"st":0,"op":15,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-455.703,-151.732,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[13.5,86.394,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[29.44,-0.144],[4.261,-0.022],[0,0],[0,0],[-8.96,0.049],[-7.791,0.041],[-39.596,0.189],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-40.537,0.152],[-7.376,0.036],[-8.838,0.046],[0,0],[0,0],[4.291,-0.023],[29.853,-0.158],[68.514,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[650,-48],[650,-1.313],[453.188,49.031],[259.374,-45.312],[59.188,47.031],[-140.812,-49.656],[-296.692,0.613],[-406.141,1.091],[-441.544,1.27],[-455.406,1.344],[-455.406,-45.344],[-441.317,-45.421],[-404.739,-45.618],[-295.707,-46.169],[-140.812,-96.688],[60.188,-2],[258.374,-96.344],[454.188,0]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.687],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.66,-2.951],[59.088,-0.222],[60.116,0.009],[14.589,0.011],[0,0],[0,0],[-29.994,-0.018],[-20.939,0.002],[-34.009,0.162],[-78.891,-0.656],[-99.891,2.656],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.687],[-100.297,2.969],[-100.89,1.312],[-98.891,0.625],[-78.891,2.313],[-34.651,0.13],[-20.15,-0.003],[-30.262,-0.023],[0,0],[0,0],[14.365,0.009],[60.522,-0.005],[68.515,-0.327],[114.703,-0.656],[99.668,-2.65],[101.11,0.344],[99.703,0]],"v":[[846,-46.969],[846,-0.281],[649.188,50.062],[455.374,-44.281],[260.188,48.062],[60.188,-48.625],[-139.384,50.288],[-296.703,1.439],[-405.21,1.388],[-455.406,1.344],[-455.406,-45.344],[-405.679,-45.306],[-295.703,-45.275],[-138.4,3.507],[60.188,-95.656],[261.188,-0.969],[454.374,-95.312],[650.188,1.031]]}],"t":7.5},{"s":[{"c":true,"i":[[-96.297,2],[-1.703,-0.688],[100.297,-2.969],[100.891,-1.312],[100.703,0.969],[100.701,0.664],[100.681,-0.572],[101,0.128],[75.997,-0.36],[0,0],[0,0],[-81.274,2.22],[-80,-0.388],[-99.304,0.78],[-99.891,-0.628],[-93.891,-1.315],[-101.11,-0.344],[-99.703,0]],"o":[[-1.703,29],[-95.703,-0.688],[-100.297,2.969],[-100.89,1.312],[-93.891,-0.346],[-99.891,-0.659],[-99.33,0.565],[-80,-0.101],[-81.589,0.387],[0,0],[0,0],[76.998,-2.103],[100.008,0.485],[100.696,-0.791],[100.109,-0.628],[99.693,1.396],[101.11,0.344],[99.703,0]],"v":[[1040,-44.029],[1040,2.659],[843.188,53.003],[649.374,-41.341],[454.188,53.003],[260.188,-46.685],[59.616,53.229],[-139.703,-47.242],[-295.701,1.017],[-455.406,1.344],[-455.406,-45.344],[-296.701,-45.241],[-139.703,-96.956],[59.601,1.447],[260.188,-96.716],[454.188,2.971],[648.374,-92.372],[844.188,3.971]]}],"t":15}],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.4824,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-0.297,-128.656],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":36}]}]}';

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { hero_title1 } = $$props;
	let { hero_title2 } = $$props;
	let { hero_description } = $$props;
	let { hero_image_1 } = $$props;
	let { hero_image_2 } = $$props;
	let { temp_image } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(6, favicon = $$props.favicon);
		if ('hero_title1' in $$props) $$invalidate(0, hero_title1 = $$props.hero_title1);
		if ('hero_title2' in $$props) $$invalidate(1, hero_title2 = $$props.hero_title2);
		if ('hero_description' in $$props) $$invalidate(2, hero_description = $$props.hero_description);
		if ('hero_image_1' in $$props) $$invalidate(3, hero_image_1 = $$props.hero_image_1);
		if ('hero_image_2' in $$props) $$invalidate(4, hero_image_2 = $$props.hero_image_2);
		if ('temp_image' in $$props) $$invalidate(5, temp_image = $$props.temp_image);
	};

	return [
		hero_title1,
		hero_title2,
		hero_description,
		hero_image_1,
		hero_image_2,
		temp_image,
		favicon
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 6,
			hero_title1: 0,
			hero_title2: 1,
			hero_description: 2,
			hero_image_1: 3,
			hero_image_2: 4,
			temp_image: 5
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div4;
	let div3;
	let div2;
	let h3;
	let t0;
	let t1;
	let div1;
	let p;
	let t2;
	let t3;
	let div0;
	let a;
	let t4_value = /*action_button*/ ctx[2].label + "";
	let t4;
	let a_href_value;

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title_1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			p = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			div0 = element("div");
			a = element("a");
			t4 = text(t4_value);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title_1*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { id: true, class: true });
			var div1_nodes = children(div1);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*content_description*/ ctx[1]);
			p_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t4 = claim_text(a_nodes, t4_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-4vykub");
			attr(p, "class", "p-large svelte-4vykub");
			attr(a, "href", a_href_value = /*action_button*/ ctx[2].url);
			attr(a, "class", "primary-small-button svelte-4vykub");
			attr(div0, "class", "button-wrapper svelte-4vykub");
			attr(div1, "id", "second");
			attr(div1, "class", "svelte-4vykub");
			attr(div2, "class", "wrapper svelte-4vykub");
			attr(div3, "class", "container svelte-4vykub");
			attr(div4, "class", "section");
			attr(div4, "id", "section-0a27aaf7");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, p);
			append_hydration(p, t2);
			append_hydration(div1, t3);
			append_hydration(div1, div0);
			append_hydration(div0, a);
			append_hydration(a, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title_1*/ 1) set_data(t0, /*content_title_1*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*action_button*/ 4 && t4_value !== (t4_value = /*action_button*/ ctx[2].label + "")) set_data(t4, t4_value);

			if (dirty & /*action_button*/ 4 && a_href_value !== (a_href_value = /*action_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title_1 } = $$props;
	let { content_description } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('content_title_1' in $$props) $$invalidate(0, content_title_1 = $$props.content_title_1);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('action_button' in $$props) $$invalidate(2, action_button = $$props.action_button);
	};

	return [content_title_1, content_description, action_button, favicon];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 3,
			content_title_1: 0,
			content_description: 1,
			action_button: 2
		});
	}
}

var commonjsGlobal = typeof globalThis !== "undefined" ? globalThis : typeof window !== "undefined" ? window : typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : {};
function getDefaultExportFromCjs(x) {
  return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, "default") ? x["default"] : x;
}
function createCommonjsModule(fn, basedir, module) {
  return module = {
    path: basedir,
    exports: {},
    require: function(path, base) {
      return commonjsRequire(path, base === void 0 || base === null ? module.path : base);
    }
  }, fn(module, module.exports), module.exports;
}
function commonjsRequire() {
  throw new Error("Dynamic requires are not currently supported by @rollup/plugin-commonjs");
}
var siema_min = createCommonjsModule(function(module, exports) {
  !function(e, t) {
    module.exports = t();
  }(typeof self != "undefined" ? self : commonjsGlobal, function() {
    return function(e) {
      function t(r) {
        if (i[r])
          return i[r].exports;
        var n = i[r] = {i: r, l: false, exports: {}};
        return e[r].call(n.exports, n, n.exports, t), n.l = true, n.exports;
      }
      var i = {};
      return t.m = e, t.c = i, t.d = function(e2, i2, r) {
        t.o(e2, i2) || Object.defineProperty(e2, i2, {configurable: false, enumerable: true, get: r});
      }, t.n = function(e2) {
        var i2 = e2 && e2.__esModule ? function() {
          return e2.default;
        } : function() {
          return e2;
        };
        return t.d(i2, "a", i2), i2;
      }, t.o = function(e2, t2) {
        return Object.prototype.hasOwnProperty.call(e2, t2);
      }, t.p = "", t(t.s = 0);
    }([function(e, t, i) {
      function r(e2, t2) {
        if (!(e2 instanceof t2))
          throw new TypeError("Cannot call a class as a function");
      }
      Object.defineProperty(t, "__esModule", {value: true});
      var n = typeof Symbol == "function" && typeof Symbol.iterator == "symbol" ? function(e2) {
        return typeof e2;
      } : function(e2) {
        return e2 && typeof Symbol == "function" && e2.constructor === Symbol && e2 !== Symbol.prototype ? "symbol" : typeof e2;
      }, s = function() {
        function e2(e3, t2) {
          for (var i2 = 0; i2 < t2.length; i2++) {
            var r2 = t2[i2];
            r2.enumerable = r2.enumerable || false, r2.configurable = true, "value" in r2 && (r2.writable = true), Object.defineProperty(e3, r2.key, r2);
          }
        }
        return function(t2, i2, r2) {
          return i2 && e2(t2.prototype, i2), r2 && e2(t2, r2), t2;
        };
      }(), l = function() {
        function e2(t2) {
          var i2 = this;
          if (r(this, e2), this.config = e2.mergeSettings(t2), this.selector = typeof this.config.selector == "string" ? document.querySelector(this.config.selector) : this.config.selector, this.selector === null)
            throw new Error("Something wrong with your selector \u{1F62D}");
          this.resolveSlidesNumber(), this.selectorWidth = this.selector.offsetWidth, this.innerElements = [].slice.call(this.selector.children), this.currentSlide = this.config.loop ? this.config.startIndex % this.innerElements.length : Math.max(0, Math.min(this.config.startIndex, this.innerElements.length - this.perPage)), this.transformProperty = e2.webkitOrNot(), ["resizeHandler", "touchstartHandler", "touchendHandler", "touchmoveHandler", "mousedownHandler", "mouseupHandler", "mouseleaveHandler", "mousemoveHandler", "clickHandler"].forEach(function(e3) {
            i2[e3] = i2[e3].bind(i2);
          }), this.init();
        }
        return s(e2, [{key: "attachEvents", value: function() {
          window.addEventListener("resize", this.resizeHandler), this.config.draggable && (this.pointerDown = false, this.drag = {startX: 0, endX: 0, startY: 0, letItGo: null, preventClick: false}, this.selector.addEventListener("touchstart", this.touchstartHandler), this.selector.addEventListener("touchend", this.touchendHandler), this.selector.addEventListener("touchmove", this.touchmoveHandler), this.selector.addEventListener("mousedown", this.mousedownHandler), this.selector.addEventListener("mouseup", this.mouseupHandler), this.selector.addEventListener("mouseleave", this.mouseleaveHandler), this.selector.addEventListener("mousemove", this.mousemoveHandler), this.selector.addEventListener("click", this.clickHandler));
        }}, {key: "detachEvents", value: function() {
          window.removeEventListener("resize", this.resizeHandler), this.selector.removeEventListener("touchstart", this.touchstartHandler), this.selector.removeEventListener("touchend", this.touchendHandler), this.selector.removeEventListener("touchmove", this.touchmoveHandler), this.selector.removeEventListener("mousedown", this.mousedownHandler), this.selector.removeEventListener("mouseup", this.mouseupHandler), this.selector.removeEventListener("mouseleave", this.mouseleaveHandler), this.selector.removeEventListener("mousemove", this.mousemoveHandler), this.selector.removeEventListener("click", this.clickHandler);
        }}, {key: "init", value: function() {
          this.attachEvents(), this.selector.style.overflow = "hidden", this.selector.style.direction = this.config.rtl ? "rtl" : "ltr", this.buildSliderFrame(), this.config.onInit.call(this);
        }}, {key: "buildSliderFrame", value: function() {
          var e3 = this.selectorWidth / this.perPage, t2 = this.config.loop ? this.innerElements.length + 2 * this.perPage : this.innerElements.length;
          this.sliderFrame = document.createElement("div"), this.sliderFrame.style.width = e3 * t2 + "px", this.enableTransition(), this.config.draggable && (this.selector.style.cursor = "-webkit-grab");
          var i2 = document.createDocumentFragment();
          if (this.config.loop)
            for (var r2 = this.innerElements.length - this.perPage; r2 < this.innerElements.length; r2++) {
              var n2 = this.buildSliderFrameItem(this.innerElements[r2].cloneNode(true));
              i2.appendChild(n2);
            }
          for (var s2 = 0; s2 < this.innerElements.length; s2++) {
            var l2 = this.buildSliderFrameItem(this.innerElements[s2]);
            i2.appendChild(l2);
          }
          if (this.config.loop)
            for (var o = 0; o < this.perPage; o++) {
              var a = this.buildSliderFrameItem(this.innerElements[o].cloneNode(true));
              i2.appendChild(a);
            }
          this.sliderFrame.appendChild(i2), this.selector.innerHTML = "", this.selector.appendChild(this.sliderFrame), this.slideToCurrent();
        }}, {key: "buildSliderFrameItem", value: function(e3) {
          var t2 = document.createElement("div");
          return t2.style.cssFloat = this.config.rtl ? "right" : "left", t2.style.float = this.config.rtl ? "right" : "left", t2.style.width = (this.config.loop ? 100 / (this.innerElements.length + 2 * this.perPage) : 100 / this.innerElements.length) + "%", t2.appendChild(e3), t2;
        }}, {key: "resolveSlidesNumber", value: function() {
          if (typeof this.config.perPage == "number")
            this.perPage = this.config.perPage;
          else if (n(this.config.perPage) === "object") {
            this.perPage = 1;
            for (var e3 in this.config.perPage)
              window.innerWidth >= e3 && (this.perPage = this.config.perPage[e3]);
          }
        }}, {key: "prev", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 ? arguments[0] : 1, t2 = arguments[1];
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            if (this.config.loop) {
              if (this.currentSlide - e3 < 0) {
                this.disableTransition();
                var r2 = this.currentSlide + this.innerElements.length, n2 = this.perPage, s2 = r2 + n2, l2 = (this.config.rtl ? 1 : -1) * s2 * (this.selectorWidth / this.perPage), o = this.config.draggable ? this.drag.endX - this.drag.startX : 0;
                this.sliderFrame.style[this.transformProperty] = "translate3d(" + (l2 + o) + "px, 0, 0)", this.currentSlide = r2 - e3;
              } else
                this.currentSlide = this.currentSlide - e3;
            } else
              this.currentSlide = Math.max(this.currentSlide - e3, 0);
            i2 !== this.currentSlide && (this.slideToCurrent(this.config.loop), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "next", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 ? arguments[0] : 1, t2 = arguments[1];
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            if (this.config.loop) {
              if (this.currentSlide + e3 > this.innerElements.length - this.perPage) {
                this.disableTransition();
                var r2 = this.currentSlide - this.innerElements.length, n2 = this.perPage, s2 = r2 + n2, l2 = (this.config.rtl ? 1 : -1) * s2 * (this.selectorWidth / this.perPage), o = this.config.draggable ? this.drag.endX - this.drag.startX : 0;
                this.sliderFrame.style[this.transformProperty] = "translate3d(" + (l2 + o) + "px, 0, 0)", this.currentSlide = r2 + e3;
              } else
                this.currentSlide = this.currentSlide + e3;
            } else
              this.currentSlide = Math.min(this.currentSlide + e3, this.innerElements.length - this.perPage);
            i2 !== this.currentSlide && (this.slideToCurrent(this.config.loop), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "disableTransition", value: function() {
          this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
        }}, {key: "enableTransition", value: function() {
          this.sliderFrame.style.webkitTransition = "all " + this.config.duration + "ms " + this.config.easing, this.sliderFrame.style.transition = "all " + this.config.duration + "ms " + this.config.easing;
        }}, {key: "goTo", value: function(e3, t2) {
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            this.currentSlide = this.config.loop ? e3 % this.innerElements.length : Math.min(Math.max(e3, 0), this.innerElements.length - this.perPage), i2 !== this.currentSlide && (this.slideToCurrent(), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "slideToCurrent", value: function(e3) {
          var t2 = this, i2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, r2 = (this.config.rtl ? 1 : -1) * i2 * (this.selectorWidth / this.perPage);
          e3 ? requestAnimationFrame(function() {
            requestAnimationFrame(function() {
              t2.enableTransition(), t2.sliderFrame.style[t2.transformProperty] = "translate3d(" + r2 + "px, 0, 0)";
            });
          }) : this.sliderFrame.style[this.transformProperty] = "translate3d(" + r2 + "px, 0, 0)";
        }}, {key: "updateAfterDrag", value: function() {
          var e3 = (this.config.rtl ? -1 : 1) * (this.drag.endX - this.drag.startX), t2 = Math.abs(e3), i2 = this.config.multipleDrag ? Math.ceil(t2 / (this.selectorWidth / this.perPage)) : 1, r2 = e3 > 0 && this.currentSlide - i2 < 0, n2 = e3 < 0 && this.currentSlide + i2 > this.innerElements.length - this.perPage;
          e3 > 0 && t2 > this.config.threshold && this.innerElements.length > this.perPage ? this.prev(i2) : e3 < 0 && t2 > this.config.threshold && this.innerElements.length > this.perPage && this.next(i2), this.slideToCurrent(r2 || n2);
        }}, {key: "resizeHandler", value: function() {
          this.resolveSlidesNumber(), this.currentSlide + this.perPage > this.innerElements.length && (this.currentSlide = this.innerElements.length <= this.perPage ? 0 : this.innerElements.length - this.perPage), this.selectorWidth = this.selector.offsetWidth, this.buildSliderFrame();
        }}, {key: "clearDrag", value: function() {
          this.drag = {startX: 0, endX: 0, startY: 0, letItGo: null, preventClick: this.drag.preventClick};
        }}, {key: "touchstartHandler", value: function(e3) {
          ["TEXTAREA", "OPTION", "INPUT", "SELECT"].indexOf(e3.target.nodeName) !== -1 || (e3.stopPropagation(), this.pointerDown = true, this.drag.startX = e3.touches[0].pageX, this.drag.startY = e3.touches[0].pageY);
        }}, {key: "touchendHandler", value: function(e3) {
          e3.stopPropagation(), this.pointerDown = false, this.enableTransition(), this.drag.endX && this.updateAfterDrag(), this.clearDrag();
        }}, {key: "touchmoveHandler", value: function(e3) {
          if (e3.stopPropagation(), this.drag.letItGo === null && (this.drag.letItGo = Math.abs(this.drag.startY - e3.touches[0].pageY) < Math.abs(this.drag.startX - e3.touches[0].pageX)), this.pointerDown && this.drag.letItGo) {
            e3.preventDefault(), this.drag.endX = e3.touches[0].pageX, this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
            var t2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, i2 = t2 * (this.selectorWidth / this.perPage), r2 = this.drag.endX - this.drag.startX, n2 = this.config.rtl ? i2 + r2 : i2 - r2;
            this.sliderFrame.style[this.transformProperty] = "translate3d(" + (this.config.rtl ? 1 : -1) * n2 + "px, 0, 0)";
          }
        }}, {key: "mousedownHandler", value: function(e3) {
          ["TEXTAREA", "OPTION", "INPUT", "SELECT"].indexOf(e3.target.nodeName) !== -1 || (e3.preventDefault(), e3.stopPropagation(), this.pointerDown = true, this.drag.startX = e3.pageX);
        }}, {key: "mouseupHandler", value: function(e3) {
          e3.stopPropagation(), this.pointerDown = false, this.selector.style.cursor = "-webkit-grab", this.enableTransition(), this.drag.endX && this.updateAfterDrag(), this.clearDrag();
        }}, {key: "mousemoveHandler", value: function(e3) {
          if (e3.preventDefault(), this.pointerDown) {
            e3.target.nodeName === "A" && (this.drag.preventClick = true), this.drag.endX = e3.pageX, this.selector.style.cursor = "-webkit-grabbing", this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
            var t2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, i2 = t2 * (this.selectorWidth / this.perPage), r2 = this.drag.endX - this.drag.startX, n2 = this.config.rtl ? i2 + r2 : i2 - r2;
            this.sliderFrame.style[this.transformProperty] = "translate3d(" + (this.config.rtl ? 1 : -1) * n2 + "px, 0, 0)";
          }
        }}, {key: "mouseleaveHandler", value: function(e3) {
          this.pointerDown && (this.pointerDown = false, this.selector.style.cursor = "-webkit-grab", this.drag.endX = e3.pageX, this.drag.preventClick = false, this.enableTransition(), this.updateAfterDrag(), this.clearDrag());
        }}, {key: "clickHandler", value: function(e3) {
          this.drag.preventClick && e3.preventDefault(), this.drag.preventClick = false;
        }}, {key: "remove", value: function(e3, t2) {
          if (e3 < 0 || e3 >= this.innerElements.length)
            throw new Error("Item to remove doesn't exist \u{1F62D}");
          var i2 = e3 < this.currentSlide, r2 = this.currentSlide + this.perPage - 1 === e3;
          (i2 || r2) && this.currentSlide--, this.innerElements.splice(e3, 1), this.buildSliderFrame(), t2 && t2.call(this);
        }}, {key: "insert", value: function(e3, t2, i2) {
          if (t2 < 0 || t2 > this.innerElements.length + 1)
            throw new Error("Unable to inset it at this index \u{1F62D}");
          if (this.innerElements.indexOf(e3) !== -1)
            throw new Error("The same item in a carousel? Really? Nope \u{1F62D}");
          var r2 = t2 <= this.currentSlide > 0 && this.innerElements.length;
          this.currentSlide = r2 ? this.currentSlide + 1 : this.currentSlide, this.innerElements.splice(t2, 0, e3), this.buildSliderFrame(), i2 && i2.call(this);
        }}, {key: "prepend", value: function(e3, t2) {
          this.insert(e3, 0), t2 && t2.call(this);
        }}, {key: "append", value: function(e3, t2) {
          this.insert(e3, this.innerElements.length + 1), t2 && t2.call(this);
        }}, {key: "destroy", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 && arguments[0], t2 = arguments[1];
          if (this.detachEvents(), this.selector.style.cursor = "auto", e3) {
            for (var i2 = document.createDocumentFragment(), r2 = 0; r2 < this.innerElements.length; r2++)
              i2.appendChild(this.innerElements[r2]);
            this.selector.innerHTML = "", this.selector.appendChild(i2), this.selector.removeAttribute("style");
          }
          t2 && t2.call(this);
        }}], [{key: "mergeSettings", value: function(e3) {
          var t2 = {selector: ".siema", duration: 200, easing: "ease-out", perPage: 1, startIndex: 0, draggable: true, multipleDrag: true, threshold: 20, loop: false, rtl: false, onInit: function() {
          }, onChange: function() {
          }}, i2 = e3;
          for (var r2 in i2)
            t2[r2] = i2[r2];
          return t2;
        }}, {key: "webkitOrNot", value: function() {
          return typeof document.documentElement.style.transform == "string" ? "transform" : "WebkitTransform";
        }}]), e2;
      }();
      t.default = l, e.exports = t.default;
    }]);
  });
});
var __pika_web_default_export_for_treeshaking__ = /* @__PURE__ */ getDefaultExportFromCjs(siema_min);
var Siema = siema_min.Siema;

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i];
	child_ctx[16] = i;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i];
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i];
	return child_ctx;
}

// (447:10) {#each content_card as card}
function create_each_block_2(ctx) {
	let div3;
	let div1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div0;
	let h60;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let h61;
	let t3_value = /*card*/ ctx[17].subtitle + "";
	let t3;
	let t4;
	let div2;
	let p;
	let t5_value = /*card*/ ctx[17].description + "";
	let t5;
	let t6;

	return {
		c() {
			div3 = element("div");
			div1 = element("div");
			img = element("img");
			t0 = space();
			div0 = element("div");
			h60 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			h61 = element("h6");
			t3 = text(t3_value);
			t4 = space();
			div2 = element("div");
			p = element("p");
			t5 = text(t5_value);
			t6 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			img = claim_element(div1_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", {});
			var h60_nodes = children(h60);
			t1 = claim_text(h60_nodes, t1_value);
			h60_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			h61 = claim_element(div0_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t3 = claim_text(h61_nodes, t3_value);
			h61_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t5 = claim_text(p_nodes, t5_value);
			p_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1yafmcq");
			attr(h61, "class", "h800");
			attr(div1, "class", "card-title-wrapper svelte-1yafmcq");
			attr(p, "class", "p-medium");
			attr(div2, "class", "card-content-wrapper svelte-1yafmcq");
			attr(div3, "class", "card-wrapper slider svelte-1yafmcq");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div1);
			append_hydration(div1, img);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t1);
			append_hydration(div0, t2);
			append_hydration(div0, h61);
			append_hydration(h61, t3);
			append_hydration(div3, t4);
			append_hydration(div3, div2);
			append_hydration(div2, p);
			append_hydration(p, t5);
			append_hydration(div3, t6);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 4 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 4 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 4 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 4 && t3_value !== (t3_value = /*card*/ ctx[17].subtitle + "")) set_data(t3, t3_value);
			if (dirty & /*content_card*/ 4 && t5_value !== (t5_value = /*card*/ ctx[17].description + "")) set_data(t5, t5_value);
		},
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

// (465:8) {#each content_card as card}
function create_each_block_1$1(ctx) {
	let div3;
	let div1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div0;
	let h60;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let h61;
	let t3_value = /*card*/ ctx[17].subtitle + "";
	let t3;
	let t4;
	let div2;
	let p;
	let t5_value = /*card*/ ctx[17].description + "";
	let t5;
	let t6;

	return {
		c() {
			div3 = element("div");
			div1 = element("div");
			img = element("img");
			t0 = space();
			div0 = element("div");
			h60 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			h61 = element("h6");
			t3 = text(t3_value);
			t4 = space();
			div2 = element("div");
			p = element("p");
			t5 = text(t5_value);
			t6 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			img = claim_element(div1_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", {});
			var h60_nodes = children(h60);
			t1 = claim_text(h60_nodes, t1_value);
			h60_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			h61 = claim_element(div0_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t3 = claim_text(h61_nodes, t3_value);
			h61_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t5 = claim_text(p_nodes, t5_value);
			p_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1yafmcq");
			attr(h61, "class", "h800");
			attr(div1, "class", "card-title-wrapper svelte-1yafmcq");
			attr(p, "class", "p-medium");
			attr(div2, "class", "card-content-wrapper svelte-1yafmcq");
			attr(div3, "class", "card-wrapper slider svelte-1yafmcq");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div1);
			append_hydration(div1, img);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t1);
			append_hydration(div0, t2);
			append_hydration(div0, h61);
			append_hydration(h61, t3);
			append_hydration(div3, t4);
			append_hydration(div3, div2);
			append_hydration(div2, p);
			append_hydration(p, t5);
			append_hydration(div3, t6);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 4 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 4 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 4 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 4 && t3_value !== (t3_value = /*card*/ ctx[17].subtitle + "")) set_data(t3, t3_value);
			if (dirty & /*content_card*/ 4 && t5_value !== (t5_value = /*card*/ ctx[17].description + "")) set_data(t5, t5_value);
		},
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

// (485:6) {#each data as d, i}
function create_each_block$1(ctx) {
	let input;
	let input_id_value;
	let input_value_value;
	let input_checked_value;
	let mounted;
	let dispose;

	function click_handler() {
		return /*click_handler*/ ctx[10](/*i*/ ctx[16]);
	}

	return {
		c() {
			input = element("input");
			this.h();
		},
		l(nodes) {
			input = claim_element(nodes, "INPUT", {
				type: true,
				id: true,
				name: true,
				class: true
			});

			this.h();
		},
		h() {
			attr(input, "type", "radio");
			attr(input, "id", input_id_value = /*i*/ ctx[16]);
			attr(input, "name", "slider-radio");
			input.value = input_value_value = /*i*/ ctx[16];
			input.checked = input_checked_value = /*select*/ ctx[5] == /*i*/ ctx[16];
			attr(input, "class", "svelte-1yafmcq");
		},
		m(target, anchor) {
			insert_hydration(target, input, anchor);
			/*input_binding*/ ctx[9](input);

			if (!mounted) {
				dispose = listen(input, "click", click_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (dirty & /*select*/ 32 && input_checked_value !== (input_checked_value = /*select*/ ctx[5] == /*i*/ ctx[16])) {
				input.checked = input_checked_value;
			}
		},
		d(detaching) {
			if (detaching) detach(input);
			/*input_binding*/ ctx[9](null);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$5(ctx) {
	let div10;
	let div9;
	let div8;
	let div4;
	let div2;
	let div0;
	let h3;
	let t0;
	let t1;
	let div1;
	let h2;
	let t2;
	let t3;
	let div3;
	let t4;
	let div6;
	let div5;
	let t5;
	let div7;
	let each_value_2 = /*content_card*/ ctx[2];
	let each_blocks_2 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_2[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let each_value_1 = /*content_card*/ ctx[2];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let each_value = /*data*/ ctx[6];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div10 = element("div");
			div9 = element("div");
			div8 = element("div");
			div4 = element("div");
			div2 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title_1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			h2 = element("h2");
			t2 = text(/*content_title_2*/ ctx[1]);
			t3 = space();
			div3 = element("div");

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].c();
			}

			t4 = space();
			div6 = element("div");
			div5 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t5 = space();
			div7 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div10 = claim_element(nodes, "DIV", { class: true, id: true });
			var div10_nodes = children(div10);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div8 = claim_element(div9_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			div4 = claim_element(div8_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title_1*/ ctx[0]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*content_title_2*/ ctx[1]);
			h2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].l(div3_nodes);
			}

			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t4 = claim_space(div8_nodes);
			div6 = claim_element(div8_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div5_nodes);
			}

			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t5 = claim_space(div8_nodes);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div7_nodes);
			}

			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-1yafmcq");
			attr(div0, "class", "hero-text-container1 svelte-1yafmcq");
			attr(h2, "class", "svelte-1yafmcq");
			attr(div1, "class", "hero-text-container2 svelte-1yafmcq");
			attr(div2, "class", "content-header-wrapper svelte-1yafmcq");
			attr(div3, "class", "card-container-desktop svelte-1yafmcq");
			attr(div4, "class", "content-wrapper svelte-1yafmcq");
			attr(div5, "class", "siema svelte-1yafmcq");
			attr(div6, "class", "card-container-mobile svelte-1yafmcq");
			attr(div7, "class", "bullet svelte-1yafmcq");
			attr(div8, "class", "wrapper svelte-1yafmcq");
			attr(div9, "class", "container svelte-1yafmcq");
			attr(div10, "class", "section");
			attr(div10, "id", "section-3a835bb8");
		},
		m(target, anchor) {
			insert_hydration(target, div10, anchor);
			append_hydration(div10, div9);
			append_hydration(div9, div8);
			append_hydration(div8, div4);
			append_hydration(div4, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t2);
			append_hydration(div4, t3);
			append_hydration(div4, div3);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				if (each_blocks_2[i]) {
					each_blocks_2[i].m(div3, null);
				}
			}

			append_hydration(div8, t4);
			append_hydration(div8, div6);
			append_hydration(div6, div5);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div5, null);
				}
			}

			append_hydration(div8, t5);
			append_hydration(div8, div7);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div7, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title_1*/ 1) set_data(t0, /*content_title_1*/ ctx[0]);
			if (dirty & /*content_title_2*/ 2) set_data(t2, /*content_title_2*/ ctx[1]);

			if (dirty & /*content_card*/ 4) {
				each_value_2 = /*content_card*/ ctx[2];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks_2[i]) {
						each_blocks_2[i].p(child_ctx, dirty);
					} else {
						each_blocks_2[i] = create_each_block_2(child_ctx);
						each_blocks_2[i].c();
						each_blocks_2[i].m(div3, null);
					}
				}

				for (; i < each_blocks_2.length; i += 1) {
					each_blocks_2[i].d(1);
				}

				each_blocks_2.length = each_value_2.length;
			}

			if (dirty & /*content_card*/ 4) {
				each_value_1 = /*content_card*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div5, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*select, radioSlider, slider*/ 56) {
				each_value = /*data*/ ctx[6];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div7, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div10);
			destroy_each(each_blocks_2, detaching);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title_1 } = $$props;
	let { content_title_2 } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_card } = $$props;
	let slider, radioSlider;
	let select = 0;
	let data = [{ val: 1 }, { val: 2 }, { val: 3 }, { val: 4 }, { val: 5 }];

	function updateSlideIndex() {
		if (this.currentSlide === -1) {
			$$invalidate(5, select = 4);
			return;
		}

		$$invalidate(5, select = this.currentSlide);
	}

	onMount(() => {
		$$invalidate(3, slider = new __pika_web_default_export_for_treeshaking__({
				selector: '.siema',
				duration: 200,
				easing: 'ease-in-out',
				perPage: {
					0: 1, // 2 items for viewport wider than 800px
					540: 2,
					865: 3, // 3 items for viewport wider than 1240px
					1020: 4
				},
				startIndex: 0,
				draggable: true,
				multipleDrag: true,
				threshold: 20,
				loop: false,
				rtl: false,
				onInit: () => {
					
				},
				onChange: updateSlideIndex
			})); // onChange: (e) => console.log("e"),
		//end Siema constructor
	}); // prev = () => {
	//     slider.prev()
	//     if (select > 0) {
	//         select--

	function input_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			radioSlider = $$value;
			$$invalidate(4, radioSlider);
		});
	}

	const click_handler = i => {
		slider.goTo(i);
	};

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(7, favicon = $$props.favicon);
		if ('content_title_1' in $$props) $$invalidate(0, content_title_1 = $$props.content_title_1);
		if ('content_title_2' in $$props) $$invalidate(1, content_title_2 = $$props.content_title_2);
		if ('content_paragraph_1' in $$props) $$invalidate(8, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_card' in $$props) $$invalidate(2, content_card = $$props.content_card);
	};

	return [
		content_title_1,
		content_title_2,
		content_card,
		slider,
		radioSlider,
		select,
		data,
		favicon,
		content_paragraph_1,
		input_binding,
		click_handler
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 7,
			content_title_1: 0,
			content_title_2: 1,
			content_paragraph_1: 8,
			content_card: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div5;
	let div4;
	let div3;
	let div2;
	let div0;
	let lottie_player;
	let lottie_player_src_value;
	let t0;
	let img;
	let img_src_value;
	let img_alt_value;
	let t1;
	let div1;
	let h3;
	let t2;
	let t3;
	let p;
	let t4;

	return {
		c() {
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			lottie_player = element("lottie-player");
			t0 = space();
			img = element("img");
			t1 = space();
			div1 = element("div");
			h3 = element("h3");
			t2 = text(/*content_title*/ ctx[0]);
			t3 = space();
			p = element("p");
			t4 = text(/*content_paragraph_1*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			lottie_player = claim_element(div0_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player).forEach(detach);
			t0 = claim_space(div0_nodes);
			img = claim_element(div0_nodes, "IMG", { src: true, alt: true, class: true });
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", {});
			var div1_nodes = children(div1);
			h3 = claim_element(div1_nodes, "H3", {});
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			t4 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[1]);
			p_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_custom_element_data(lottie_player, "autoplay", "");
			set_custom_element_data(lottie_player, "loop", "");
			set_custom_element_data(lottie_player, "mode", "normal");
			set_custom_element_data(lottie_player, "class", "lottie svelte-1skabwk");
			if (!src_url_equal(lottie_player.src, lottie_player_src_value = trianglesLottie)) set_custom_element_data(lottie_player, "src", lottie_player_src_value);
			if (!src_url_equal(img.src, img_src_value = /*content_image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*content_image*/ ctx[2].alt);
			attr(img, "class", "svelte-1skabwk");
			attr(div0, "class", "img-wrapper svelte-1skabwk");
			attr(p, "class", "p-large");
			attr(div2, "class", "section-container content svelte-1skabwk");
			attr(div3, "class", "wrapper svelte-1skabwk");
			attr(div4, "class", "container svelte-1skabwk");
			attr(div5, "class", "section");
			attr(div5, "id", "section-13ad9037");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, lottie_player);
			append_hydration(div0, t0);
			append_hydration(div0, img);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, h3);
			append_hydration(h3, t2);
			append_hydration(div1, t3);
			append_hydration(div1, p);
			append_hydration(p, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_image*/ 4 && !src_url_equal(img.src, img_src_value = /*content_image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_image*/ 4 && img_alt_value !== (img_alt_value = /*content_image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_title*/ 1) set_data(t2, /*content_title*/ ctx[0]);
			if (dirty & /*content_paragraph_1*/ 2) set_data(t4, /*content_paragraph_1*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div5);
		}
	};
}

const trianglesLottie = '{"nm":"Композиция 1","ddd":0,"h":600,"w":600,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":4,"nm":"Слой-фигура 6","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-130,-236,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[218,142,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100.929,103.144,0],"t":41,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[160,62,0],"t":112,"ti":[0,0,0],"to":[0,0,0]},{"s":[218,142,0],"t":142.000005783779}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[0],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[90],"t":46},{"s":[0],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[-160,-256],[-132,-206],[-96,-250]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"Слой-фигура 5","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[92,244,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[396,494,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[414,550,0],"t":76,"ti":[0,0,0],"to":[0,0,0]},{"s":[396,494,0],"t":142.000005783779}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":0.97},"s":[0],"t":0},{"o":{"x":0.333,"y":-0.026},"i":{"x":0.667,"y":1},"s":[-90.515],"t":46},{"s":[0],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[66,218],[58,272],[128,248]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"Слой-фигура 3","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[56,26,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[196,462,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[74,546,0],"t":25,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[266.838,415.226,0],"t":99,"ti":[0,0,0],"to":[0,0,0]},{"s":[196,462,0],"t":142.000005783779}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[0],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[267],"t":46},{"s":[0],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[44,-24],[16,50],[92,38]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"Слой-фигура 2","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[142,28,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[460,356,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[518,430,0],"t":80,"ti":[0,0,0],"to":[0,0,0]},{"s":[460,356,0],"t":113.000004602584}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[0],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[113],"t":46},{"s":[0],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[190,-4],[96,2],[156,62]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4},{"ty":4,"nm":"Слой-фигура 7","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-138,114,0],"ix":1},"s":{"a":0,"k":[38.277,38.277,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[342,300,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[518,228,0],"t":64,"ti":[0,0,0],"to":[0,0,0]},{"s":[342,300,0],"t":142.000005783779}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[92],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[44],"t":46},{"s":[92],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[-56,-84],[-154,92],[44,92]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[-56.825,10.677],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-144.031,111.33],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5},{"ty":4,"nm":"Слой-фигура 1","sr":1,"st":0,"op":300.00001221925,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-138,114,0],"ix":1},"s":{"a":0,"k":[64.4,64.4,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[174,288,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[147.415,364.338,0],"t":27,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[110,284,0],"t":93,"ti":[0,0,0],"to":[0,0,0]},{"s":[174,288,0],"t":132.00000537647}],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[0],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[110],"t":46},{"s":[0],"t":86.0000035028518}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Фигура 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Контур 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[-56,-84],[-154,92],[44,92]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Заливка 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[-56.825,10.677],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-144.031,111.33],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6}],"v":"5.10.2","fr":29.9700012207031,"op":143.000005824509,"ip":0,"assets":[]}';

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_image } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_image' in $$props) $$invalidate(2, content_image = $$props.content_image);
	};

	return [content_title, content_paragraph_1, content_image, favicon];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			favicon: 3,
			content_title: 0,
			content_paragraph_1: 1,
			content_image: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let div4;
	let div3;
	let div2;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t0;
	let div1;
	let p;
	let t1;
	let t2;
	let div0;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t3;
	let img2;
	let img2_src_value;
	let img2_alt_value;

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			img0 = element("img");
			t0 = space();
			div1 = element("div");
			p = element("p");
			t1 = text(/*content_paragraph_1*/ ctx[0]);
			t2 = space();
			div0 = element("div");
			img1 = element("img");
			t3 = space();
			img2 = element("img");
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			img0 = claim_element(div2_nodes, "IMG", { class: true, src: true, alt: true });
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[0]);
			p_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			img1 = claim_element(div0_nodes, "IMG", { class: true, src: true, alt: true });
			t3 = claim_space(div0_nodes);
			img2 = claim_element(div0_nodes, "IMG", { class: true, src: true, alt: true });
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img0, "class", "content-image-1 svelte-1wdf4m2");
			if (!src_url_equal(img0.src, img0_src_value = /*content_image_1*/ ctx[1].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*content_image_1*/ ctx[1].alt);
			attr(p, "class", "p-large");
			attr(img1, "class", "content-image-3 svelte-1wdf4m2");
			if (!src_url_equal(img1.src, img1_src_value = /*content_image_3*/ ctx[3].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*content_image_3*/ ctx[3].alt);
			attr(img2, "class", "content-image-2 svelte-1wdf4m2");
			if (!src_url_equal(img2.src, img2_src_value = /*content_image_2*/ ctx[2].url)) attr(img2, "src", img2_src_value);
			attr(img2, "alt", img2_alt_value = /*content_image_2*/ ctx[2].alt);
			attr(div0, "class", "content-image-wrapper svelte-1wdf4m2");
			attr(div1, "class", "section-container content svelte-1wdf4m2");
			attr(div2, "class", "wrapper svelte-1wdf4m2");
			attr(div3, "class", "container svelte-1wdf4m2");
			attr(div4, "class", "section");
			attr(div4, "id", "section-bc4b1933");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			append_hydration(div2, img0);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, p);
			append_hydration(p, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			append_hydration(div0, img1);
			append_hydration(div0, t3);
			append_hydration(div0, img2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_image_1*/ 2 && !src_url_equal(img0.src, img0_src_value = /*content_image_1*/ ctx[1].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*content_image_1*/ 2 && img0_alt_value !== (img0_alt_value = /*content_image_1*/ ctx[1].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*content_paragraph_1*/ 1) set_data(t1, /*content_paragraph_1*/ ctx[0]);

			if (dirty & /*content_image_3*/ 8 && !src_url_equal(img1.src, img1_src_value = /*content_image_3*/ ctx[3].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*content_image_3*/ 8 && img1_alt_value !== (img1_alt_value = /*content_image_3*/ ctx[3].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*content_image_2*/ 4 && !src_url_equal(img2.src, img2_src_value = /*content_image_2*/ ctx[2].url)) {
				attr(img2, "src", img2_src_value);
			}

			if (dirty & /*content_image_2*/ 4 && img2_alt_value !== (img2_alt_value = /*content_image_2*/ ctx[2].alt)) {
				attr(img2, "alt", img2_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_image_1 } = $$props;
	let { content_image_2 } = $$props;
	let { content_image_3 } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('content_paragraph_1' in $$props) $$invalidate(0, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_image_1' in $$props) $$invalidate(1, content_image_1 = $$props.content_image_1);
		if ('content_image_2' in $$props) $$invalidate(2, content_image_2 = $$props.content_image_2);
		if ('content_image_3' in $$props) $$invalidate(3, content_image_3 = $$props.content_image_3);
	};

	return [
		content_paragraph_1,
		content_image_1,
		content_image_2,
		content_image_3,
		favicon
	];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 4,
			content_paragraph_1: 0,
			content_image_1: 1,
			content_image_2: 2,
			content_image_3: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div7;
	let div6;
	let div5;
	let div2;
	let div0;
	let h30;
	let t0;
	let t1;
	let div1;
	let h31;
	let t2;
	let t3;
	let div4;
	let p;
	let t4;
	let t5;
	let div3;
	let a;
	let t6_value = /*action_button*/ ctx[3].label + "";
	let t6;
	let a_href_value;

	return {
		c() {
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			div2 = element("div");
			div0 = element("div");
			h30 = element("h3");
			t0 = text(/*content_title_1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			h31 = element("h3");
			t2 = text(/*content_title_2*/ ctx[1]);
			t3 = space();
			div4 = element("div");
			p = element("p");
			t4 = text(/*content_description*/ ctx[2]);
			t5 = space();
			div3 = element("div");
			a = element("a");
			t6 = text(t6_value);
			this.h();
		},
		l(nodes) {
			div7 = claim_element(nodes, "DIV", { class: true, id: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div2 = claim_element(div5_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h30 = claim_element(div0_nodes, "H3", { class: true });
			var h30_nodes = children(h30);
			t0 = claim_text(h30_nodes, /*content_title_1*/ ctx[0]);
			h30_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h31 = claim_element(div1_nodes, "H3", { class: true });
			var h31_nodes = children(h31);
			t2 = claim_text(h31_nodes, /*content_title_2*/ ctx[1]);
			h31_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { id: true, class: true });
			var div4_nodes = children(div4);
			p = claim_element(div4_nodes, "P", { class: true });
			var p_nodes = children(p);
			t4 = claim_text(p_nodes, /*content_description*/ ctx[2]);
			p_nodes.forEach(detach);
			t5 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			a = claim_element(div3_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t6 = claim_text(a_nodes, t6_value);
			a_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h30, "class", "svelte-uqq91j");
			attr(div0, "class", "hero-text-container1 svelte-uqq91j");
			attr(h31, "class", "svelte-uqq91j");
			attr(div1, "class", "hero-text-container2 svelte-uqq91j");
			attr(div2, "class", "svelte-uqq91j");
			attr(p, "class", "p-large svelte-uqq91j");
			attr(a, "href", a_href_value = /*action_button*/ ctx[3].url);
			attr(a, "class", "primary-small-button svelte-uqq91j");
			attr(div3, "class", "button-wrapper svelte-uqq91j");
			attr(div4, "id", "second");
			attr(div4, "class", "svelte-uqq91j");
			attr(div5, "class", "wrapper svelte-uqq91j");
			attr(div6, "class", "container svelte-uqq91j");
			attr(div7, "class", "section");
			attr(div7, "id", "section-0c854e7c");
		},
		m(target, anchor) {
			insert_hydration(target, div7, anchor);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h30);
			append_hydration(h30, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, h31);
			append_hydration(h31, t2);
			append_hydration(div5, t3);
			append_hydration(div5, div4);
			append_hydration(div4, p);
			append_hydration(p, t4);
			append_hydration(div4, t5);
			append_hydration(div4, div3);
			append_hydration(div3, a);
			append_hydration(a, t6);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title_1*/ 1) set_data(t0, /*content_title_1*/ ctx[0]);
			if (dirty & /*content_title_2*/ 2) set_data(t2, /*content_title_2*/ ctx[1]);
			if (dirty & /*content_description*/ 4) set_data(t4, /*content_description*/ ctx[2]);
			if (dirty & /*action_button*/ 8 && t6_value !== (t6_value = /*action_button*/ ctx[3].label + "")) set_data(t6, t6_value);

			if (dirty & /*action_button*/ 8 && a_href_value !== (a_href_value = /*action_button*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div7);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title_1 } = $$props;
	let { content_title_2 } = $$props;
	let { content_description } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('content_title_1' in $$props) $$invalidate(0, content_title_1 = $$props.content_title_1);
		if ('content_title_2' in $$props) $$invalidate(1, content_title_2 = $$props.content_title_2);
		if ('content_description' in $$props) $$invalidate(2, content_description = $$props.content_description);
		if ('action_button' in $$props) $$invalidate(3, action_button = $$props.action_button);
	};

	return [content_title_1, content_title_2, content_description, action_button, favicon];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			favicon: 4,
			content_title_1: 0,
			content_title_2: 1,
			content_description: 2,
			action_button: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let div3;
	let div2;
	let div1;
	let div0;
	let h3;
	let t0;
	let t1;
	let p;
	let t2;
	let t3;
	let lottie_player;
	let lottie_player_src_value;

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p = element("p");
			t2 = text(/*content_paragraph_1*/ ctx[1]);
			t3 = space();
			lottie_player = element("lottie-player");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[1]);
			p_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);

			lottie_player = claim_element(div0_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player).forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "p-large");
			set_custom_element_data(lottie_player, "autoplay", "");
			set_custom_element_data(lottie_player, "loop", "");
			set_custom_element_data(lottie_player, "mode", "normal");
			set_custom_element_data(lottie_player, "class", "lottie svelte-16r7h0q");
			if (!src_url_equal(lottie_player.src, lottie_player_src_value = stairsToSuccessLottie)) set_custom_element_data(lottie_player, "src", lottie_player_src_value);
			attr(div0, "class", "section-container content svelte-16r7h0q");
			attr(div1, "class", "wrapper svelte-16r7h0q");
			attr(div2, "class", "container svelte-16r7h0q");
			attr(div3, "class", "section");
			attr(div3, "id", "section-06c53dd8");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p);
			append_hydration(p, t2);
			append_hydration(div0, t3);
			append_hydration(div0, lottie_player);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_paragraph_1*/ 2) set_data(t2, /*content_paragraph_1*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

const stairsToSuccessLottie = '{"nm":"Heaven Stairs","ddd":0,"h":500,"w":500,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":4,"nm":"Ball","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,15,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"s":true,"x":{"a":0,"k":268.771,"ix":3},"y":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[207.799],"t":5},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[208.438],"t":6},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[209.616],"t":7},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[211.474],"t":8},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[214.222],"t":9},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[218.209],"t":10},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[224.081],"t":11},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[233.313],"t":12},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[250.203],"t":13},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[263.103],"t":14},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[254.509],"t":15},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[240.685],"t":16},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[231.944],"t":17},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[225.889],"t":18},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[221.394],"t":19},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[217.937],"t":20},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[215.23],"t":21},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[213.098],"t":22},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[211.424],"t":23},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[210.126],"t":24},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[209.144],"t":25},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[208.433],"t":26},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[207.958],"t":27},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[207.689],"t":28},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[207.799],"t":35},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[208.438],"t":36},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[209.616],"t":37},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[211.474],"t":38},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[214.222],"t":39},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[218.209],"t":40},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[224.081],"t":41},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[233.313],"t":42},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[250.203],"t":43},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[263.103],"t":44},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[254.509],"t":45},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[240.685],"t":46},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[231.944],"t":47},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[225.889],"t":48},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[221.394],"t":49},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[217.937],"t":50},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[215.23],"t":51},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[213.098],"t":52},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[211.424],"t":53},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[210.126],"t":54},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[209.144],"t":55},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[208.433],"t":56},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[207.958],"t":57},{"s":[207.689],"t":58}]},"z":{"a":0,"k":0}},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.005,-2.5],[0,15],[-14.995,-2.5]]}],"t":0},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.004,-2.362],[0,15],[-14.996,-2.362]]}],"t":1},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.004,-2.004],[0,15],[-14.996,-2.004]]}],"t":2},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.003,-1.516],[0,15],[-14.997,-1.516]]}],"t":3},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.002,-0.984],[0,15],[-14.998,-0.984]]}],"t":4},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.001,-0.496],[0,15],[-14.999,-0.496]]}],"t":5},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,-0.138],[0,15],[-15,-0.138]]}],"t":6},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":7},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.654,0],[0,15],[-14.654,0]]}],"t":8},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.863,0],[0,15],[-13.863,0]]}],"t":9},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.82,0],[0,15],[-12.82,0]]}],"t":10},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.639,0],[0,15],[-11.639,0]]}],"t":11},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.495,0],[0,15],[-10.495,0]]}],"t":12},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.365,0],[0,15],[-13.365,0]]}],"t":13},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":14},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0.25,-9.75],[15.005,3.5],[0,15],[-14.995,3.5]]}],"t":15},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":16},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.495,0],[0,15],[-10.495,0]]}],"t":17},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.869,-0.207],[0,15],[-10.868,-0.207]]}],"t":18},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.262,-0.425],[0,15],[-11.261,-0.425]]}],"t":19},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.66,-0.646],[0,15],[-11.658,-0.646]]}],"t":20},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.057,-0.866],[0,15],[-12.054,-0.866]]}],"t":21},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.451,-1.084],[0,15],[-12.447,-1.084]]}],"t":22},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.84,-1.3],[0,15],[-12.835,-1.3]]}],"t":23},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.222,-1.511],[0,15],[-13.216,-1.511]]}],"t":24},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.593,-1.717],[0,15],[-13.586,-1.717]]}],"t":25},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.951,-1.916],[0,15],[-13.944,-1.916]]}],"t":26},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.29,-2.104],[0,15],[-14.282,-2.104]]}],"t":27},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.601,-2.276],[0,15],[-14.592,-2.276]]}],"t":28},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.863,-2.421],[0,15],[-14.854,-2.421]]}],"t":29},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.005,-2.5],[0,15],[-14.995,-2.5]]}],"t":30},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.004,-2.362],[0,15],[-14.996,-2.362]]}],"t":31},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.004,-2.004],[0,15],[-14.996,-2.004]]}],"t":32},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.003,-1.516],[0,15],[-14.997,-1.516]]}],"t":33},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.002,-0.984],[0,15],[-14.998,-0.984]]}],"t":34},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15.001,-0.496],[0,15],[-14.999,-0.496]]}],"t":35},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,-0.138],[0,15],[-15,-0.138]]}],"t":36},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":37},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.654,0],[0,15],[-14.654,0]]}],"t":38},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.863,0],[0,15],[-13.863,0]]}],"t":39},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.82,0],[0,15],[-12.82,0]]}],"t":40},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.639,0],[0,15],[-11.639,0]]}],"t":41},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.495,0],[0,15],[-10.495,0]]}],"t":42},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.365,0],[0,15],[-13.365,0]]}],"t":43},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":44},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0.25,-9.75],[15.005,3.5],[0,15],[-14.995,3.5]]}],"t":45},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[15,0],[0,15],[-15,0]]}],"t":46},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.495,0],[0,15],[-10.495,0]]}],"t":47},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[10.869,-0.207],[0,15],[-10.868,-0.207]]}],"t":48},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.262,-0.425],[0,15],[-11.261,-0.425]]}],"t":49},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[11.66,-0.646],[0,15],[-11.658,-0.646]]}],"t":50},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.057,-0.866],[0,15],[-12.054,-0.866]]}],"t":51},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.451,-1.084],[0,15],[-12.447,-1.084]]}],"t":52},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[12.84,-1.3],[0,15],[-12.835,-1.3]]}],"t":53},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.222,-1.511],[0,15],[-13.216,-1.511]]}],"t":54},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.593,-1.717],[0,15],[-13.586,-1.717]]}],"t":55},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[13.951,-1.916],[0,15],[-13.944,-1.916]]}],"t":56},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.29,-2.104],[0,15],[-14.282,-2.104]]}],"t":57},{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.601,-2.276],[0,15],[-14.592,-2.276]]}],"t":58},{"s":[{"c":true,"i":[[-8.284,0],[0,-8.284],[8.284,0],[0,8.284]],"o":[[8.284,0],[0,8.284],[-8.284,0],[0,-8.284]],"v":[[0,-15],[14.863,-2.421],[0,15],[-14.854,-2.421]]}],"t":59}]}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":2,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9373,0.7922,0.102],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":0,"nm":"Stairs","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[115,77,0],"ix":1},"s":{"a":0,"k":[-100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[217.505,296.603,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":230,"h":154,"refId":"comp_0","ind":2},{"ty":4,"nm":"Gate","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,134.641,0],"ix":1},"s":{"a":0,"k":[46,46,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[265.5,263.578,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[25.611,0],[0,-25.611],[0,0],[0,0],[0,0],[-50.343,0],[0,-50.344]],"o":[[0,0],[0,0],[0,-25.611],[-25.611,0],[0,0],[0,0],[0,0],[0,-50.344],[50.344,0],[0,0]],"v":[[91.301,134.641],[46.448,134.641],[46.448,-43.34],[0,-89.787],[-46.448,-43.34],[-46.448,134.641],[-91.301,134.641],[-91.301,-43.34],[0,-134.641],[91.301,-43.34]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":8,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}}],"ind":3},{"ty":4,"nm":"GateBev","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,134.641,0],"ix":1},"s":{"a":0,"k":[46,46,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[272.5,263.578,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[25.611,0],[0,-25.611],[0,0],[0,0],[0,0],[-50.343,0],[0,-50.344]],"o":[[0,0],[0,0],[0,-25.611],[-25.611,0],[0,0],[0,0],[0,0],[0,-50.344],[50.344,0],[0,0]],"v":[[91.301,134.641],[46.448,134.641],[46.448,-43.34],[0,-89.787],[-46.448,-43.34],[-46.448,134.641],[-91.301,134.641],[-91.301,-43.34],[0,-134.641],[91.301,-43.34]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.498,0.7412],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":8,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}}],"ind":4},{"ty":4,"nm":"BG","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[250,250,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[500,500],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,1,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5}],"v":"5.7.12","fr":30,"op":60,"ip":0,"assets":[{"nm":"Stairs","id":"comp_0","layers":[{"ty":4,"nm":"Shape Layer 2","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[119.39,-9.835,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80,126],[-111.5,126],[-111.5,53.5],[29.5,53.5]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[96.5,126],[-111.5,126],[-111.5,53.5],[28,53.5]]}],"t":2},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[83.5,126],[-111.5,126],[-111.5,53.5],[15.688,53.5]]}],"t":24},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[81,126],[-111.5,126],[-111.5,53.5],[15.688,53.5]]}],"t":28},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.25,126],[-111.5,126],[-111.5,53.5],[30.063,53.5]]}],"t":29},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.25,126],[-111.5,126],[-111.5,53.5],[30.063,53.5]]}],"t":31},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[96.5,126],[-111.5,126],[-111.5,53.5],[28,53.5]]}],"t":32},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[82.5,127],[-111.5,126],[-111.5,53.5],[14.063,54.5]]}],"t":55},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.75,127],[-111.5,126],[-111.5,53.5],[14.062,54.5]]}],"t":58},{"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80,126],[-111.5,126],[-111.5,53.5],[29.5,53.5]]}],"t":59}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":2,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"Shape Layer 1","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"td":1,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,99.218,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[119.39,-9.835,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[209.21,-13.863],[209.42,59.016],[-18.5,58.816],[-18.71,-14.062]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0,0.5647],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-91.415,68.816],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"Layer 8 :M 2","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"tt":1,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[274.473,250,0],"ix":1},"s":{"a":0,"k":[40,40,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[118.864,81.165,0],"t":0,"ti":[5.669,6.281,0],"to":[-5.669,-6.281,0]},{"s":[84.847,43.482,0],"t":60}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 8","ix":1,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0.6431,0.7569],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[422.46,415.745],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 7","ix":2,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3804,0.9059,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[380.178,368.389],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 6","ix":3,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0.6431,0.7569],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[337.896,321.033],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 5","ix":4,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3804,0.9059,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[295.614,273.678],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 4","ix":5,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0.6431,0.7569],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[253.332,226.322],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 3","ix":6,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3804,0.9059,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[211.051,178.967],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 2","ix":7,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0.6431,0.7569],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[168.769,131.611],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Layer 1","ix":8,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[136.751,23.678],[-136.751,23.678],[-136.751,-23.678],[136.751,-23.678]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3804,0.9059,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[126.487,84.255],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"Shape Layer 3","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[119.39,-9.835,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"a","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-2.633,39],[-134,39],[-134,146.742],[-2.633,146.742]]},"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80,126],[-111.5,126],[-111.5,53.5],[29.5,53.5]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[96.5,126],[-111.5,126],[-111.5,53.5],[28,53.5]]}],"t":2},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[83.5,126],[-111.5,126],[-111.5,53.5],[15.688,53.5]]}],"t":24},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[81,126],[-111.5,126],[-111.5,53.5],[15.688,53.5]]}],"t":28},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.25,126],[-111.5,126],[-111.5,53.5],[30.063,53.5]]}],"t":29},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.25,126],[-111.5,126],[-111.5,53.5],[30.063,53.5]]}],"t":31},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[96.5,126],[-111.5,126],[-111.5,53.5],[28,53.5]]}],"t":32},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[82.5,127],[-111.5,126],[-111.5,53.5],[14.063,54.5]]}],"t":55},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80.75,127],[-111.5,126],[-111.5,53.5],[14.062,54.5]]}],"t":58},{"s":[{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[80,126],[-111.5,126],[-111.5,53.5],[29.5,53.5]]}],"t":59}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":2,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4}]}]}';

function instance$9($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
	};

	return [content_title, content_paragraph_1, favicon];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			favicon: 2,
			content_title: 0,
			content_paragraph_1: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$a(ctx) {
	let div5;
	let div4;
	let div3;
	let div2;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div1;
	let lottie_player;
	let lottie_player_src_value;
	let t1;
	let div0;
	let a;
	let t2_value = /*content_action*/ ctx[1].label + "";
	let t2;
	let a_href_value;

	return {
		c() {
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			img = element("img");
			t0 = space();
			div1 = element("div");
			lottie_player = element("lottie-player");
			t1 = space();
			div0 = element("div");
			a = element("a");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			img = claim_element(div2_nodes, "IMG", { class: true, src: true, alt: true });
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			lottie_player = claim_element(div1_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player).forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "class", "content-image svelte-x50bhh");
			if (!src_url_equal(img.src, img_src_value = /*content_image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*content_image*/ ctx[0].alt);
			set_custom_element_data(lottie_player, "autoplay", "");
			set_custom_element_data(lottie_player, "loop", "");
			set_custom_element_data(lottie_player, "mode", "normal");
			set_custom_element_data(lottie_player, "class", "lottie svelte-x50bhh");
			if (!src_url_equal(lottie_player.src, lottie_player_src_value = eyesLottie)) set_custom_element_data(lottie_player, "src", lottie_player_src_value);
			attr(a, "href", a_href_value = /*content_action*/ ctx[1].url);
			attr(a, "class", "primary-small-button svelte-x50bhh");
			attr(div0, "class", "button-wrapper svelte-x50bhh");
			attr(div1, "class", "content-2 svelte-x50bhh");
			attr(div2, "class", "section-container content svelte-x50bhh");
			attr(div3, "class", "wrapper svelte-x50bhh");
			attr(div4, "class", "container svelte-x50bhh");
			attr(div5, "class", "section");
			attr(div5, "id", "section-88d4f99e");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			append_hydration(div2, img);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, lottie_player);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_image*/ 1 && !src_url_equal(img.src, img_src_value = /*content_image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_image*/ 1 && img_alt_value !== (img_alt_value = /*content_image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_action*/ 2 && t2_value !== (t2_value = /*content_action*/ ctx[1].label + "")) set_data(t2, t2_value);

			if (dirty & /*content_action*/ 2 && a_href_value !== (a_href_value = /*content_action*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div5);
		}
	};
}

const eyesLottie = '{"nm":"Vector shape animation 51","ddd":0,"h":1080,"w":1080,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":3,"nm":"Null 6","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[140,140,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[540,540,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":1},{"ty":3,"nm":"Null 5","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[30,30,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[-205.714,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":2,"parent":1},{"ty":3,"nm":"Null 4","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":0},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":20},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":30},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":35},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":38},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":41},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":50.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":52.464},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":54.22},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":57.146},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":63},{"o":{"x":0.167,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":74.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":83},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":99},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":109},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":114},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":117},{"s":[100,106,100],"t":120.0000048877}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":3,"parent":2},{"ty":3,"nm":"Null 4","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":0},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":20},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":30},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":35},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":38},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":41},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":50.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":52.464},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":54.22},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":57.146},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":63},{"o":{"x":0.167,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":74.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":83},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":99},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":109},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":114},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":117},{"s":[100,99,100],"t":120.0000048877}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":4,"parent":2},{"ty":4,"nm":"Layer 11 - Group 2 - Group 4","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"td":1,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1373,0.749,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5,"parent":4},{"ty":4,"nm":"Layer 11 - Group 2 - Group 1","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"tt":1,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[570.781,516.246,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[0,0,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[200,0,0],"t":30,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[-206.667,40,0],"t":60,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[140,0,0],"t":90,"ti":[0,0,0],"to":[0,0,0]},{"s":[0,0,0],"t":120.0000048877}],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[21.569,21.569],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1176,0,0.3451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[570.781,516.246],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6,"parent":2},{"ty":4,"nm":"Layer 11 - Group 2 - Group 3","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.2824,0.8471,0.949],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":7,"parent":4},{"ty":4,"nm":"Layer 11 - Group 2 - Group 5","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":8,"parent":3},{"ty":3,"nm":"Null 5","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[30,30,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[205.714,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":9,"parent":1},{"ty":3,"nm":"Null 4","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":0},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":20},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":30},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":35},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":38},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":41},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":50.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":52.464},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":54.22},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":57.146},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":63},{"o":{"x":0.167,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":74.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":83},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":99},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":109},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,106,100],"t":114},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,7,100],"t":117},{"s":[100,106,100],"t":120.0000048877}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":10,"parent":9},{"ty":3,"nm":"Null 4","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":0},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":20},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":30},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":35},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":38},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":41},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":50.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":52.464},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":54.22},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":57.146},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":63},{"o":{"x":0.167,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":74.708},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":83},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":99},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":109},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,99,100],"t":114},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[100,0,100],"t":117},{"s":[100,99,100],"t":120.0000048877}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":11,"parent":9},{"ty":4,"nm":"Layer 11 - Group 2 - Group 9","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"td":1,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1373,0.749,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":12,"parent":11},{"ty":4,"nm":"Layer 11 - Group 2 - Group 8","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"tt":1,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[570.781,516.246,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[0,0,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[200,0,0],"t":30,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[-206.667,40,0],"t":60,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.66,"y":0},"i":{"x":0.34,"y":1},"s":[140,0,0],"t":90,"ti":[0,0,0],"to":[0,0,0]},{"s":[0,0,0],"t":120.0000048877}],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[21.569,21.569],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1176,0,0.3451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[570.781,516.246],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":13,"parent":9},{"ty":4,"nm":"Layer 11 - Group 2 - Group 7","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.2824,0.8471,0.949],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":14,"parent":11},{"ty":4,"nm":"Layer 11 - Group 2 - Group 6","sr":1,"st":0,"op":3892.00015852441,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[572.231,514.88,0],"ix":1},"s":{"a":0,"k":[1216.019,1216.019,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[0,0,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[33.304,0],[0,0],[0,0],[-33.304,0]],"o":[[0,0],[0,33.304],[0,0],[0,0],[0,-33.304],[0,0]],"v":[[30.151,-30.151],[30.151,-30.151],[-30.151,30.151],[-30.151,30.151],[-30.151,30.151],[30.151,-30.151]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[572.231,514.88],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":15,"parent":10}],"v":"5.10.1","fr":29.9700012207031,"op":121.000004928431,"ip":0,"assets":[]}';

function instance$a($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_image } = $$props;
	let { content_action } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('content_image' in $$props) $$invalidate(0, content_image = $$props.content_image);
		if ('content_action' in $$props) $$invalidate(1, content_action = $$props.content_action);
	};

	return [content_image, content_action, favicon];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$a, create_fragment$a, safe_not_equal, {
			favicon: 2,
			content_image: 0,
			content_action: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (70:4) {#each nav as { link }}
function create_each_block$2(ctx) {
	let h6;
	let a;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let a_target_value;
	let a_href_value;
	let t1;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { id: true, class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { target: true, class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(h6_nodes);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "target", a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self');

			attr(a, "class", "link svelte-14fdjq7");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(h6, "id", "links");
			attr(h6, "class", "h950 svelte-14fdjq7");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t0);
			append_hydration(h6, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*nav*/ 1 && a_target_value !== (a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self')) {
				attr(a, "target", a_target_value);
			}

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$b(ctx) {
	let div;
	let footer;
	let nav_1;
	let t0;
	let span;
	let p;
	let t1;
	let each_value = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");
			footer = element("footer");
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			p = element("p");
			t1 = text(/*copyright*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			footer = claim_element(div_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav_1 = claim_element(footer_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			nav_1_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			p = claim_element(span_nodes, "P", { id: true, class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, /*copyright*/ ctx[1]);
			p_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav_1, "class", "svelte-14fdjq7");
			attr(p, "id", "copyright");
			attr(p, "class", "p-small svelte-14fdjq7");
			attr(span, "class", "svelte-14fdjq7");
			attr(footer, "class", "section-container svelte-14fdjq7");
			attr(div, "class", "section");
			attr(div, "id", "section-84b44e1e");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, footer);
			append_hydration(footer, nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, p);
			append_hydration(p, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*nav*/ 1) {
				each_value = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*copyright*/ 2) set_data(t1, /*copyright*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { nav } = $$props;
	let { copyright } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
		if ('copyright' in $$props) $$invalidate(1, copyright = $$props.copyright);
	};

	return [nav, copyright, favicon];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$b, create_fragment$b, safe_not_equal, { favicon: 2, nav: 0, copyright: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$c($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$c, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$c(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let t10;
	let component_11;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"size": 3
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/investor", "label": "Investor" }
					}
				],
				site_nav_button: { "url": "/portal", "label": "Get Started" }
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				hero_title1: "Welcome to",
				hero_title2: "UNLOK",
				hero_description: "Unleash the Power of Blockchain Rewards",
				hero_image_1: {
					"alt": "Earn Redeem Repeat",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686517485291earn-redeem-repeat%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686517485291earn-redeem-repeat%20copy.svg",
					"size": 14
				},
				hero_image_2: {
					"alt": "Rewards Tier 3",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002150000reward-tiers-app-lines%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002150000reward-tiers-app-lines%20copy.svg",
					"size": 43
				},
				temp_image: {
					"alt": "Crown",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686772060000Crown%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686772060000Crown%20copy.svg",
					"size": 6
				}
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title_1: "Join the UNLOK Community and Get Rewarded",
				content_description: "Get ready to embark on an exciting journey of rewards and adventure with UNLOK. Our innovative platform is designed to bring joy and excitement to your everyday life. Earn UNLOK tokens, unlock exclusive perks, and explore a world of possibilities.",
				action_button: {
					"url": "/portal",
					"label": "Get Started "
				}
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title_1: "Discover the",
				content_title_2: "UNLOK Experience",
				content_paragraph_1: "At UNLOK, we believe in offering more than just traditional rewards. Our platform encompasses a comprehensive ecosystem that empowers merchants and consumers to explore new horizons and unlock a world of possibilities. Discover the diverse components of our ecosystem:",
				content_card: [
					{
						"image": {
							"alt": "UnlokPay",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"size": 14
						},
						"title": "UnlokPay",
						"subtitle": "Pay with Ease",
						"description": "Say goodbye to boring payment methods. With UNLOKPAY, you can make payments effortlessly without any transaction charges. Shop at your favourite stores, dine at the trendiest restaurants, and enjoy seamless transactions."
					},
					{
						"image": {
							"alt": "UnlokMarket",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"size": 6
						},
						"title": "UnlokMarket",
						"subtitle": "Shop Your Heart Out",
						"description": "Get ready for a shopping spree like no other! UNLOKMARKET is your go-to destination for the coolest products and services. Discover unique NFTs, trendy fashion, tech gadgets, and more, all in one place."
					},
					{
						"image": {
							"alt": "UnlokGC",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"size": 7
						},
						"title": "UnlokGC",
						"subtitle": "Trade Gift Cards for Fun",
						"description": "Got unused gift cards lying around? Trade them for UNLOK tokens or other digital goodies! UNLOKGC lets you exchange your gift cards instantly, so you can treat yourself to something you truly love."
					},
					{
						"image": {
							"alt": "UnlokDebit",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"size": 5
						},
						"title": "UnlokDebit",
						"subtitle": "Spend with Style ",
						"description": "Level up your spending game with UNLOKDEBIT. It's not just a regular debit card—it's a statement. Manage your digital assets and make secure transactions while showcasing your unique style."
					},
					{
						"image": {
							"alt": "UnlokReward",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"size": 9
						},
						"title": "UnlokReward",
						"subtitle": "Unlock Exclusive Bonuses",
						"description": "Prepare to be spoiled with UNLOKREWARD! Enjoy exclusive perks, discounts on airfare, and access to limited edition NFTs. Our community is all about giving you the VIP treatment you deserve."
					}
				]
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Be Rewarded Every Step of the Way",
				content_paragraph_1: "Get ready for the thrill of earning high yields and bonuses with UNLOK. Our engaging staking mechanism ensures that you're constantly reaping the rewards. The more you engage, the more fun you'll have and the more you'll earn!",
				content_image: {
					"alt": "Congrats you earned a reward",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002090000Congrats%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002090000Congrats%20copy.svg",
					"size": 149
				}
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_paragraph_1: "We've partnered with NetCents, a leading global cryptocurrency payments processor, to bring you even more convenience and opportunities. With access to over 75 million merchants worldwide, your UNLOK journey is set to be extraordinary.",
				content_image_1: {
					"alt": "Join Forces to Earn Rewards",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686439648633Frame%201261153238%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686439648633Frame%201261153238%20copy.svg",
					"size": 43
				},
				content_image_2: {
					"alt": "City",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686004134000city-outlined-bg%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686004134000city-outlined-bg%20copy.svg",
					"size": 63
				},
				content_image_3: {
					"alt": "Crypto Technology",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687471250977crypto-tech.svg.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687471250977crypto-tech.svg.svg",
					"size": 20
				}
			}
		});

	component_7 = new Component$8({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title_1: "Tokenomics",
				content_title_2: "Made Fun and Fair",
				content_description: "At UNLOK, we believe in fairness and sustainability. Our token distribution ensures that everyone gets a fair chance to participate and benefit from the platform's growth. As a member, you'll enjoy ongoing rewards and an exciting ecosystem.",
				action_button: {
					"url": "/tokenomics",
					"label": "Learn about tokenomics"
				}
			}
		});

	component_8 = new Component$9({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Get Ready to UNLOK the Fun!",
				content_paragraph_1: "Are you ready to unleash the fun and excitement? Join the UNLOK revolution and redefine the way you experience rewards. Get started today, and let's embark on this incredible adventure together!"
			}
		});

	component_9 = new Component$a({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_image: {
					"alt": "Join the Comunity",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686440899353join-the-community%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686440899353join-the-community%20copy.svg",
					"size": 58
				},
				content_action: { "url": "/portal", "label": "Get Started" }
			}
		});

	component_10 = new Component$b({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				nav: [
					{
						"link": {
							"url": "/tokenomics",
							"label": "Tokenomics"
						}
					},
					{
						"link": {
							"url": "/privacy",
							"label": "Privacy Policy"
						}
					},
					{
						"link": {
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/Whitepaper.pdf?t=2023-06-23T23%3A35%3A42.985Z",
							"label": "Whitepaper"
						}
					},
					{
						"link": {
							"url": "https://unlokloyalty.com#contact-us",
							"label": "Contact Us"
						}
					}
				],
				copyright: "© 2023 UNLOK. All rights reserved."
			}
		});

	component_11 = new Component$c({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
			t10 = space();
			create_component(component_11.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
			t10 = claim_space(nodes);
			claim_component(component_11.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			insert_hydration(target, t10, anchor);
			mount_component(component_11, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			transition_in(component_11.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			transition_out(component_11.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
			if (detaching) detach(t10);
			destroy_component(component_11, detaching);
		}
	};
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$c, safe_not_equal, {});
	}
}

export default Component$d;
