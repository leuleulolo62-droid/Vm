-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'ysZkcP4rmgt1AkRVCzzHbulM'
local __p = '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b1NgemNaSXhXW1p1VVN6WldmB1xZUF0dS0tydmMhSXs/VUxwWSU/CBc/RkFDCRFGaUZgZ3RIVHFRWUxtSkFrRVpkGFJNVkAGeUVjbmpWcGhCVUwWSkcHS0NtFCQIBABeM1h8OCYNUmVQR1l/V0doR0NwB0NfSUABbUtyZ3dNTmZTR0Vhc1N6S0MLB0cwR1QMYT03NTcVCHtMGwk6UV5oWFBoGkNeS1QRclljeHVDVmhCRFh7TV1qXkp8PlJNR1Rqcl0PdmNHWh4HFhgiC0B0BQYnHF9fU0UAb1xqemNaSXpSW1V0VVN6WldlDVxYVV0dS0tydmMhSX8/VUxwWSU/CBc/RkFDCRFGaUZgY3FIVHpWWUxtSkFqRVthGFJNVkAHc0VnYGpWcGhCVUwWSksHS0NtFCQIBABeM1h8OCYNUmVQQV15V0ptR0NwB0BcSUQCbUtyZ3dMQ2ZSQUVhc1N6S0MLB0swR1QMYT03NTcVCHtMGwk6UV5oXlJpGktdS1QRclljeHJLVmhCRFh7TV1jWUp8PlJNR1RqdVsPdmNHWh4HFhgiC0B0BQYnHF9fUUQBb11remNaSHFQW1l5VVN6WldjBVxZX10dS0tydmMhTnk/VUxwWSU/CBc/RkFDCRFGaUZgYXJDVHxQWUxtS0poRVdnGFJNVkAHdUVhYGpWcGhCVUwWTUEHS0NtFCQIBABeM1h8OCYNUmVQQlR5V0RtR0NwB0JYSUEJbUtyZ3dMTGZUQ0Vhc1N6S0MLAEEwR1QMYT03NTcVCHtMGwk6UV5oU1ZnGkpVS1QRc1NjeHVLVmhCRFh7Sl1tWkp8PlJNR1RqdV8PdmNHWh4HFhgiC0B0BQYnHF9fXkICb1pqemNaSHFWW1t+VVN6WldmAlxZVl0dS0tydmMhTn0/VUxwWSU/CBc/RkFDCRFGaUZhZXRDVHpQWUxtS0puRVtmGFJNVkcAc0VkYmpWcGhCVUwWTUUHS0NtFCQIBABeM1h8OCYNUmVRTFh8V0dtR0NwBktZSUMGbUtyZ3dMTWZXTUVhc1N6S0MLAEUwR1QMYT03NTcVCHtMGwk6UV5pUlpjGkZdS1QRc1JkeHVIVmhCRFh7Tl1qX0p8PlJNR1RqdVMPdmNHWh4HFhgiC0B0BQYnHF9ZVkUAb15lemNaSHFXW1V+VVN6WldmB1xeXl0dS0tydmMhTnE/VUxwWSU/CBc/RkFDCRFGaUZmZ3tDVH5UWUxtS0puRVphGFJNVkAHdEVnZWpWcGhCVUwWTEMHS0NtFCQIBABeM1h8OCYNUmVWR1V7V0BvR0NwBktZSUMJbUtyZ3dMQ2ZTTEVhc1N6S0MLAUMwR1QMYT03NTcVCHtMGwk6UV5uWFJoGkNUS1QRcl9jeHRIVmhCRFh7Tl1oXkp8PlJNR1RqdFkPdmNHWh4HFhgiC0B0BQYnHF9ZVEUGb1pnemNaSXxQW1t4VVN6WlBjAlxZUl0dS0tydmMhT3s/VUxwWSU/CBc/RkFDCRFGaUZmZHpKVHBWWUxtSkVjRVZoGFJNVkcBcEVqZGpWcGhCVUwWTEcHS0NtFCQIBABeM1h8OCYNUmVWRFR7V0ZqR0NwB0RVSUcBbUtyZ3BKS2ZaRkVhc1N6S0MLAUcwR1QMYT03NTcVCHtMGwk6UV5uWlVgGkBfS1QRcl1qeHNDVmhCRF50QF1vUkp8PlJNR1RqdF0PdmNHWh4HFhgiC0B0BQYnHF9ZV0EFb15hemNaSX9TW1h0VVN6WlBgBFxbXl0dS0tydmMhT38/VUxwWSU/CBc/RkFDCRFGaUZmZnFJVHFRWUxtSkRoRVRlGFJNVkcBcUVnb2pWcGhCVUwWTEsHS0NtFCQIBABeM1h8OCYNUmVWRV19V0prR0NwB0tdSUUFbUtyZ3BKSGZTREVhc1N6S0MLAUswR1QMYT03NTcVCHtMGwk6UV5uW1JgGkNaS1QRclJieHNIVmhCRF9/Sl1tW0p8PlJNR1Rqd1sPdmNHWh4HFhgiC0B0BQYnHF9ZV0QIb11jemNaSXFTW1x6VVN6WldiDVxZU10dS0tydmMhTHk/VUxwWSU/CBc/RkFDCRFGaUZmZnNNVHFaWUxtSktjRVppGFJNVkAGeEVnY2pWcGhCVUwWT0EHS0NtFCQIBABeM1h8OCYNUmVWRVx0V0duR0NwB0tcSUwEbUtyZ3VKT2ZSR0Vhc1N6S0MLAkEwR1QMYT03NTcVCHtMGwk6UV5uWlBiGkVcS1QRclJheHJJVmhCRFp8SV1oXEp8PlJNR1Rqd18PdmNHWh4HFhgiC0B0BQYnHF9ZVkMCb1xiemNaSXFaW1h6VVN6WlVhBVxZVl0dS0tydmMhTH0/VUxwWSU/CBc/RkFDCRFGaUZmZXNPVHBXWUxtSkppRVBkGFJNVkIBeEVlZGpWcGhCVUwWT0UHS0NtFCQIBABeM1h8OCYNUmVWRlh1V0tsR0NwB0tVSUcEbUtyZ3VKTGZaQEVhc1N6S0MLAkUwR1QMYT03NTcVCHtMGwk6UV5uWFdnGkpYS1QRdVtmeHtOVmhCRFl6Sl1uW0p8PlJNR1Rqd1MPdmNHWh4HFhgiC0B0BQYnHF9ZVEAIb1xnemNaTnlSW1h8VVN6WldkDVxVVl0dS0tydmMhTHE/VUxwWSU/CBc/RkFDCRFGaUZmZXdMVH5RWUxtTUBoRVpkGFJNVkcIcEVlZGpWcGhCVUwWTkMHS0NtFCQIBABeM1h8OCYNUmVWR197V0tqR0NwAEFVSUcGbUtyZ3BDSWZSRkVhc1N6S0MLA0MwR1QMYT03NTcVCHtMGwk6UV5uWlJgGkpdS1QRdV9meHRMVmhCRF90S11rW0p8PlJNR1RqdlkPdmNHWh4HFhgiC0B0BQYnHF9ZV0EBb15qemNaTn1QW1R7VVN6WldoAlxUVl0dS0tydmMhTXs/VUxwWSU/CBc/RkFDCRFGaUZmZnpDVHlSWUxtTUZpRVVlGFJNVkEGcEVmZ2pWcGhCVUwWTkcHS0NtFCQIBABeM1h8OCYNUmVWRFR/V0poR0NwAEdfSUEGbUtyZ3ZOT2ZWTUVhc1N6S0MLA0cwR1QMYT03NTcVCHtMGwk6UV5uWVRhGkZZS1QRdV5reHZOVmhCRFl/QV1oU0p8PlJNR1Rqdl0PdmNHWh4HFhgiC0B0BQYnHF9ZVEIBb15hemNaTn5bW199VVN6WlZiDFxVVV0dS0tydmMhTX8/VUxwWSU/CBc/RkFDCRFGaUZmY3RMVHFTWUxtTUViRVpkGFJNVkEDdUVhY2pWcGhCVUwWTksHS0NtFCQIBABeM1h8OCYNUmVWQFt0V0FqR0NwAERUSUQCbUtyZ3BMS2ZVRUVhc1N6S0MLA0swR1QMYT03NTcVCHtMGwk6UV5uXldhGkFUS1QRdV1reHNOVmhCRF94SF1vW0p8PlJNR1RqeVsPdmNHWh4HFhgiC0B0BQYnHF9ZU0MHb1lhemNaTn5bW118VVN6WldkAFxbXl0dS0tydmMhQnk/VUxwWSU/CBc/RkFDCRFGaUZmYnVKVH5UWUxtTUViRVtoGFJNVkYCdkVqZ2pWcGhCVUwWQUEHS0NtFCQIBABeM1h8OCYNUmVXRl95V0tuR0NwAEVcSUAEbUtyZ3dCSmZTRUVhc1N6S0MLDEEwR1QMYT03NTcVCHtMGwk6UV5vWFpgGkdcS1QRdVxleHtCVmhCRFh6TF1qW0p8PlJNR1RqeV8PdmNHWh4HFhgiC0B0BQYnHF9YUUIAb1lnemNaTnBUW197VVN6WlBkAVxYUV0dS0tydmMhQn0/VUxwWSU/CBc/RkFDCRFGaUZnbnpKVH1WWUxtTUtvRVRmGFJNVkEHcEVkbmpWcGhCVUwWQUUHS0NtFCQIBABeM1h8OCYNUmVURFR5V0doR0NwAEpbSUEGbUtyZ3dJSGZWTEVhc1N6S0MLDEUwR1QMYT03NTcVCHtMGwk6UV5sX1tpGkNfS1QRdVNkeHZMVmhCRF91S11iWEp8PlJNR1RqeVMPdmNHWh4HFhgiC0B0BQYnHF9bX0QJb1pnemNaT3pTW1x7VVN6WldoAlxZVF0dS0tydmMhQnE/VUxwWSU/CBc/RkFDCRFGaUZkbnRMVHFTWUxtTUtvRVJhGFJNVkAJdkVmZWpWcGhCVUwWQEMHS0NtFCQIBABeM1h8OCYNUmVaRll8V0JvR0NwAEpfSUIAbUtyZ3dCQmZVQEVhc1N6S0MLDUMwR1QMYT03NTcVCHtMGwk6UV5iXltiGkRcS1QRdVJreHVLVmhCRFh1QF1tXUp8PlJNR1RqeFkPdmNHWh4HFhgiC0B0BQYnHF9VX0UDb1NmemNaTnFaW151VVN6WldoAVxdV10dS0tydmMhQ3s/VUxwWSU/CBc/RkFDCRFGaUZqb3NJVH9aWUxtTENvRVNnGFJNVkAGdkVkZGpWcGhCVUwWQEcHS0NtFCQIBABeM1h8OCYNUmVbRFh0V0FuR0NwAUJfSUQGbUtyZ3BDS2ZVQkVhc1N6S0MLDUcwR1QMYT03NTcVCHtMGwk6UV5jXVdmGkReS1QRdFpreHRDVmhCRFh0T11sWUp8PlJNR1RqeF0PdmNHWh4HFhgiC0B0BQYnHF9UXkQDb1NremNaTnFbW156VVN6WldoBVxbXl0dS0tydmMhQ38/VUxwWSU/CBc/RkFDCRFGaUZjZnJOQmZUQkBtTUpsRVVmGFJNVkAGdUVrZWpWcGhCVUwWQEsHS0NtFCQIBABeM1h8OCYNUmVTRV50T11jXE9wAEZeSUcJbUtyZ3dCQmZUTEVhc1N6S0MLDUswR1QMYT03NTcVCHtMGwk6UV5rW1BmB1xfUVgRdl9qeHRLVmhCRlh5SF1vXkp8PlJNR1RqcFtiC2NHWh4HFhgiC0B0BQYnHF9cV0AId0VnYm9aTXxbW1x5VVN6WFViAVxdX10dS0tydmMhS3hTKExwWSU/CBc/RkFDCRFGaUZjZnpLSGZSTUBtTkdjRVRkGFJNVEECdUVrY2pWcGhCVUwWSENoNkNtFCQIBABeM1h8OCYNUmVTRVV1S11jUk9wA0deSUMFbUtyZXVLSmZaREVhc1N6S0MLBUJeOlQMYT03NTcVCHtMGwk6UV5rWlFoBlxZXlgRdl9qeHtNVmhCRlp/SF1pWEp8PlJNR1RqcFtmC2NHWh4HFhgiC0B0BQYnHF9cVkEGdkVlYm9aTX1XW1h4VVN6WFZjAVxeVF0dS0tydmMhS3hXKExwWSU/CBc/RkFDCRFGaUZjZ3tPSGZTREBtTkdiRVpoGFJNVEIDdUVmZWpWcGhCVUwWSENsNkNtFCQIBABeM1h8OCYNUmVTR11/QF1tU09wA0ZVSUMBbUtyZXZOTmZXQ0Vhc1N6S0MLBUJaOlQMYT03NTcVCHtMGwk6UV5rWVFmDVxeUFgRdl5meHVNVmhCRll6Tl1tU0p8PlJNR1RqcFtqC2NHWh4HFhgiC0B0BQYnHF9cVEUGdUVkb29aTX1UW1h0VVN6WFZoAlxVVF0dS0tydmMhS3hbKExwWSU/CBc/RkFDCRFGaUZjZXdKSGZTREBtTkZrRVFlGFJNVEMBdUVkb2pWcGhCVUwWSEJqNkNtFCQIBABeM1h8OCYNUmVTRlh/Tl1iXU9wA0ZVSUwCbUtyZXBPS2ZXQ0Vhc1N6S0MLBUNcOlQMYT03NTcVCHtMGwk6UV5rWFVhDVxVU1gRdl9reHNOVmhCRl96S11pWkp8PlJNR1RqcFpgC2NHWh4HFhgiC0B0BQYnHF9cVEIAcEVlZG9aTXxaW1R4VVN6WFFhA1xfV10dS0tydmMhS3lRKExwWSU/CBc/RkFDCRFGaUZjZXtDS2ZbTUBtTkdiRVpkGFJNVEYBcEVkY2pWcGhCVUwWSEJuNkNtFCQIBABeM1h8OCYNUmVTRlt/S11iXE9wA0ZVSUMJbUtyZXdCSmZWRkVhc1N6S0MLBUNYOlQMYT03NTcVCHtMGwk6UV5rWFRiBlxVVlgRdl9qeHVJVmhCRlt/QV1tXEp8PlJNR1RqcFpkC2NHWh4HFhgiC0B0BQYnHF9cU0QAeEVmbm9aTXxbW119VVN6WFplA1xbUl0dS0tydmMhS3lVKExwWSU/CBc/RkFDCRFGaUZjYnNKSGZQQEBtTkdiRVRkGFJNVEQHcUVlb2pWcDVof0FgWZHO54HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z6Xl3RkOyoPBNR0IGYSUTAAo9OxwrOiJtLjIDOywZeiY+R1xmDjkeEmNIU2hCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUyv7fFQRk5w1ub5heCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffIPh4CBBVdYSUTABwqNQEsIT8SLkF6VkMrPlJNR1RqcDZydmNHWh4HFhgiC0B0BQYnHF9eXkcfdlN+dnZKTmZTRUBtSl1vXEp8PlJNR1RqczZydmNHWh4HFhgiC0B0BQYnHF9eXk0fdV9+dnZKTmZTRUBtT0t0WlZ5GHhNR1QRGlgPdmNaR2g0EA85FgFpRQ01Q1pAVE0Ib15jemNPSnxMRFxhWUJpWE1hBVtBbVQRYUsJYh5aWmhfVTooGgc1GVB+WhcaT1kCeFx8YXdWWn1SRUJ8Tl96WlpgGkdcTlg7YUtydhhPJ2hCVVFtLxY5HwwiB1wDAgMZbFhrbm1PSWRCQFx9V0JtR0NkB0ZDUEUYbWFydmNaIX4/VUxtRFMMDgAkWwBeSRpUNkN/YnNLVHlbWUx4SUN0W1B8FEZbVFoAdUJ+XGNaWmg5QjFtWVNnSzU1VwYCFUcfLw4lfm5JTn1MR15hWUZqW01gB15NU0IEb1pif29wWmhCVTd1JFN6S15wYhcOExtDckU8MzRSV3tWQ0J0Sl96XlFnGkNdS1QEdl18YnBTVkJCVUxtIkoHS0NwCVI7AhdFLhlheC0fDWBPQVl1V0dvR0NlBkVDVkQdYV5lYG1DSGFOf0xtWVMBWlMNFFJQRyJUIh89JHBUFC0VXUF5TEB0XVF8FEdYU1oAcUdyYnVOVHxUXEBHWVN6SzhhBS9NR0kRFw4xIiwISWYMEBtlVEBuWE1nBl5NUkEFb1piemNOTHBMRFVkVXl6S0Nwb0NfOlQRfEsEMyAOFTpRWwIoDlt3WFdnGkVfS1QEeVp8Z3RWWn1aQkJ8SVp2YUNwFFI2VkdsYUtvdhUfGTwNB19jFxYtQ05kAUdDUE0dYV5qZ21LTWRCQFt6V0VrQk9aFFJNRy8AdTZydn5aLC0BAQM/Sl00DhR4GUZYVloFcEdyYHNCVHlVWUx5T0B0WFZ5GHhNR1QRGlpnC2NaR2g0EA85FgFpRQ01Q1pAU0QBb1JnemNMSnBMRFthWUdtW01hA1tBbVQRYUsJZ3UnWmhfVTooGgc1GVB+WhcaT1kFcVl8Z3dWWn5SQkJ0T196XVNpGkpYTlg7YUtydhhLTRVCVVFtLxY5HwwiB1wDAgMZbF9iZm1CS2RCQ1x7V0ZrR0NmA0FDVUAYbWFydmNaIXlaKExtRFMMDgAkWwBeSRpUNkN/YnFIVH1UWUx7SUR0X1p8FEVfUVoCeEJ+XGNaWmg5RFUQWVNnSzU1VwYCFUcfLw4lfm5OS3tMQFthWUVqU01hAl5NUEIDb19if29wWmhCVTd/SS56S15wYhcOExtDckU8MzRSV3xSRUJ+S196XVNnGkBdS1QGeFl8b3VTVkJCVUxtIkFrNkNwCVI7AhdFLhlheC0fDWBPQVx8V0JtR0NmBEdDUkEdYVNmb21IT2FOf0xtWVMBWVENFFJQRyJUIh89JHBUFC0VXUF5QEB0WVd8FERdUloHdEdyZ3NPSmZWQEVhc1N6S0MLBkEwR1QMYT03NTcVCHtMGwk6UV5uW1Z+A0ZBR0IBdkVjYm9aS3pXQ0J8SFp2YUNwFFI2VUBsYUtvdhUfGTwNB19jFxYtQ05kBEBDX0AdYV1jYG1CT2RCRF9+SV1pXkp8PlJNR1Rqc14PdmNHWh4HFhgiC0B0BQYnHF9ZV0QfcFp+dnVKT2ZaQEBtSEduUk1mA1tBbVQRYUsJZHUnWmhfVTooGgc1GVB+WhcaT1kFdVl8Z3pWWn5QQkJ8Tl96WlZkB1xbV10dS0tydmMhSH8/VUxwWSU/CBc/RkFDCRFGaUZmYnFUSHlOVVp/T11vX09wBUdUUFoFeEJ+XGNaWmg5R1QQWVNnSzU1VwYCFUcfLw4lfm5OSXFMTV1hWUVqWE1oBV5NVkMAcEVqb2pWcGhCVUwWS0oHS0NtFCQIBABeM1h8OCYNUmVWRltjTkR2S1VhB1xZVlgRcFxqY21CS2FOf0xtWVMBWFMNFFJQRyJUIh89JHBUFC0VXUF+QEt0WFV8FERdUloGeEdyZ3tCS2ZSRkVhc1N6S0MLB0MwR1QMYT03NTcVCHtMGwk6UV5uW1Z+AEJBR0IAd0VjZm9aS3FXQUJ/SVp2YUNwFFI2VEZsYUtvdhUfGTwNB19jFxYtQ05kBEZDVk0dYV1iYG1DTmRCR1x4S11sU0p8PlJNR1RqclgPdmNHWh4HFhgiC0B0BQYnHF9ZV0QfeFx+dnVLTWZURUBtS0JpUk1lDVtBbVQRYUsJZXcnWmhfVTooGgc1GVB+WhcaT1kCeFJ8YXRWWn5SQ0J0SV96WVFiAVxfVF0dS0tydmMhSX0/VUxwWSU/CBc/RkFDCRFGaUZmZnJUSH1OVVp8TV1rXE9wBkFdUVoGd0J+XGNaWmg5RloQWVNnSzU1VwYCFUcfLw4lfm5OSnpMRl5hWUVoWk1mAl5NVUABdEVgZmpWcGhCVUwWSkQHS0NtFCQIBABeM1h8OCYNUmVWRV5jQER2S1ViBVxYX1gRclpnZG1KTWFOf0xtWVMBWFsNFFJQRyJUIh89JHBUFC0VXUF5SUR0WVd8FERfVVoCdkdyZXBITmZQQEVhc1N6S0MLB0swR1QMYT03NTcVCHtMGwk6UV5rU1p+BkJBR0IDcEVnYm9aSXtRTEJ8TFp2YUNwFFI2U0RsYUtvdhUfGTwNB19jFxYtQ05hA0RDV0UdYV1gZ21MQ2RCRl58Sl1pWEp8PlJNR1RqdVoPdmNHWh4HFhgiC0B0BQYnHF9cV0Afc1x+dnVIS2ZVRUBtSkFrWk1mAVtBbVQRYUsJYnEnWmhfVTooGgc1GVB+WhcaT1kAcF98YXVWWn5QREJ4TF96WFdkAFxaU10dS0tydmMhTns/VUxwWSU/CBc/RkFDCRFGaUZgYHVUTXhOVVp/SF1vX09wB0ZZVVoBeEJ+XGNaWmg5QVgQWVNnSzU1VwYCFUcfLw4lfm5IT3FMRFlhWUVoWk1mAF5NVEIAckVhb2pWcGhCVUwWTUYHS0NtFCQIBABeM1h8OCYNUmVbQkJ8Sl96XVFkGkdZS1QCd1hkeHFCU2RoVUxtWShuXT5wFE9NMRFSNQQgZW0UHz9KWFl5TF1rXU9wAkBcSUwBbUthYHNJVH9QXEBHWVN6SzhkAy9NR0kRFw4xIiwISWYMEBtlVEZoWE1jDV5NUUYAb15qemNJTXFVW1R7UF9QS0NwFClZXykRYVZyACYZDicQRkIjHARyRlJiBVxaUVgRd1ljeHVPVmhRQlV4V0duQk9aFFJNRy8FeDZydn5aLC0BAQM/Sl00DhR4GUZYSUEEbUtkZHJUQ3hOVV91T0R0U1V5GHhNR1QRGl5iC2NaR2g0EA85FgFpRQ01Q1pcVUcFb1tiemNMSHpMRVRhWUBiXVd+A0dES34RYUtyDXZLJ2hCSEwbHBAuBBFjGhwIEFwAcllreHdMVmhURFtjTUV2S1BoAURDVkwYbWFydmNaIX1QKExtRFMMDgAkWwBeSRpUNkNjY3BOVHtUWUx7S0d0XFR8FEFaXk0feVp7eklaWmhCLll+JFN6VkMGUREZCAYCbwU3IWtLTX1VW195VVNsWFV+DUVBR0cIdV18bntTVkJCVUxtIkZuNkNwCVI7AhdFLhlheC0fDWBTTFl/V0pvR0NmB0NDX0UdYVhlb3RUT3FLWWZtWVN6MFZlaVJNWlRnJAgmOTFJVCYHAkR/SENoRVdmGFJbVEIfeFN+dnBDTHBMQFpkVXl6S0Nwb0dbOlQRfEsEMyAOFTpRWwIoDltoWFJgGkNfS1QHcFJ8Z3pWWntaQF1jQUJzR2lwFFJNPEEGHEtya2MsHysWGh5+Vx0/HEtiAEJYSU0CbUtkZHVUS3lOVV91T0p0WlV5GHhNR1QRGl5qC2NaR2g0EA85FgFpRQ01Q1pfUkAGb1JiemNMSX9MTVRhWUBiXFd+DERES34RYUtyDXZDJ2hCSEwbHBAuBBFjGhwIEFwDdlpieHRJVmhURl5jQUp2S1BoAkRDVEMYbWFydmNaIX5SKExtRFMMDgAkWwBeSRpUNkNgYXBMVHtVWUx4TkB0UlV8FEFVUEcfc1J7eklaWmhCLlp8JFN6VkMGUREZCAYCbwU3IWtIQnxXW1p5VVNvXFV+B0RBR0cJdlp8ZHZTVkJCVUxtIkVoNkNwCVI7AhdFLhlheC0fDWBQTF15V0ZuR0NmBEBDU0wdYVhqYXtUQ3hLWWZtWVN6MFVjaVJNWlRnJAgmOTFJVCYHAkR/QERqRVNlGFJYUEEfcVl+dnBCTXlMRV1kVXl6S0Nwb0RZOlQRfEsEMyAOFTpRWwIoDltpW1dpGkRYS1QEeFt8Y3dWWntaQ1RjTkJzR2lwFFJNPEIEHEtya2MsHysWGh5+Vx0/HEtjBUpaSUQIbUtnbnJUTXBOVV91T0R0XFN5GHhNR1QRGl1kC2NaR2g0EA85FgFpRQ01Q1peVUICb1NiemNPQ3hMTVVhWUBiXFJ+DENES35MS2F/e2OY7sSA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwtNwV2VCl/jPWVMeMi0ReTsuRzpwF0sCGQo0LhtCXT86EAc5AwYjFBAIEwNUJAVyAXJaGyYGVTt/UFN6S0NwFFJNR1QRYUtytNf4cGVPVY7Z7ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr27WYhFhA7B0MedSQyNzt4Dz8Bdn5aNAk0KjwCMD0OODwHBXhnSlkREhs3NSobFmgVFBU9Fho0H0MzWxwJDgBYLgUhXC8VGSkOVT8dPDATKi8PYzM0Nzt4Dz8Bdn5aAUJCVUxtIkAHS15wT3hNR1QRYUtydjcDCi1CSExvDhIzHzw0UQEdBgNfY0dYdmNaWmhCVUwiGxk/CBcjFE9NHFZGLhk5JTMbGS1MOzwOWVV6Owo1UxdDJRVdLVpwemNYDScQHh89GBA/RS0Ad1JLRyRYJAw3eAEbFiRTWy4sFR8fBQdyGFJPEBtDKhgiNyAfVAYyNkxrWSMzDgQ1GjAMCxgAbykzOi8pCikVG05hWVEtBBE7RwIMBBEfDzsRdmVaKiEHEgljOxI2B1J+fxsBCzZQLQdwK0laWmhCCEBHWVN6SzhhAS9NWlRKS0tydmNaWmhCARU9HFNnS0EnVRsZOABYLA4gdG9wWmhCVUxtWVM1CQk1VwZNWlQTNgQgPTAKGysHWycoABA7GxB+dgAEAxNUbykgPycdH3lMIQUgHAF4YUNwFFIQS34RYUtyDXJNJ2hfVRdHWVN6S0NwFFIZHgRUYVZydDQbEzw9AR84FxI3AkF8PlJNR1QRYUtyIjAPFCkPHExwWVEtBBE7RwIMBBEfDzsRdmVaKiEHEgljLQAvBQI9XUNDMwdELwo/P2FWcGhCVUxtWVN6Hwo9UQA9BgZFYVZydDQVCCMRBQ0uHF0UOyBwElI9DhFWJEUGJTYUGyULREIZEB4/GTMxRgZPS34RYUtydmNaWjsDEwkCHxUpDhdwCVI7AhdFLhlheC0fDWBSWUx9VVN3XlN5PlJNR1RMbWFydmNaIXlaKExwWQhQS0NwFFJNR1RFOBs3dn5aWD8DHBgSDhI2BxByGHhNR1QRYUtydjQbFiQwVVFtWwQ1GQgjRBMOAlp/EShycGMqEy0FEEIOFgEoAgc/RiYfBgQfFgo+OhFYVkJCVUxtWVN6SxQxWB4hR0kRYxw9JCgJCikBEEIDKTB6TUMAXRcKAlpyLhkgPycVCBwQFBxjLhI2By9yPlJNR1RMbWFydmNaIXlbKExwWQhQS0NwFFJNR1RFOBs3dn5aWD8DHBgSFRIsCkF8PlJNR1QRYUtyOiIMGxgDBxhtRFN4HAwiXwEdBhdUbyUCFWNcWhgLEAsoVz87HQIEWwUIFVp9IB0zBiIIDmpoVUxtWQ5QFmlaGV9NheC9o//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ub9bVkcYYnG1GNaLQEsVTwBOCcfSyAfejQkICcRYUM8Ny4fWmNCEBQsGgd6BgYxRwcfAhARMQQhPzcTFSZLVUxtWVN6S0NwFJD55X4cbEuwwteY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1fNYe25aLQcwOShtSHk2BAAxWFI+MzV2BDQFHw0lOQ4lKjt8WU56EGlwFFJNPEZsYUtvdjgYFicBHiIsFBZnSTQ5WjABCBdacEl+dmMKFTtfIwkuDRwoWE0+UQVFSkUCb1tqemNaTWZSTEBtWVNoU1Z+DUVES1QRLwokEy0eR3lOVUwkHQtnWh58PlJNR1RqcjZydn5aASoOGg8mNxI3Dl5yYxsDJRheIgBgdG9aWjgNBlEbHBAuBBFjGhwIEFwccFN8ZHNWWmhUW1V6VVN6S1ZgAlxdX10dYUs8NzU/FCxfRkBtWRo+E15iSV5nR1QRYTBmC2NaR2gZFwAiGhgUCg41CVA6DhpzLQQxPXBYVmhCBQM+RCU/CBc/RkFDCRFGaUZgZ21DSGRCVVt4V0diR0NwA0VYSUUBaEdydi0bDA0MEVF7VVN6AgcoCUEQS34RYUtyDXYnWmhfVRcvFRw5AC0xWRdQRSNYLyk+OSARTmpOVUw9FgBnPQYzQB0fVFpfJBx6e3JNVH1bWUxtTkR0WlZ8FFJcVkQJb1trf29aFCkUMAIpREJuR0M5UApQUwkdS0tydmMhTBVCVVFtAhE2BAA7ehMAAkkTFgI8FC8VGSNXV0BtWQM1GF4GUREZCAYCbwU3IWtXS39MRVxhWVNtXE1hAV5NR0UFcFt8Y3NTVmgMFBoIFxdnWlV8FBsJH0kEPEdYdmNaWhNVKExtRFMhCQ8/VxkjBhlUfEkFPy04FicBHlpvVVN6GwwjCSQIBABeM1h8OCYNUmVXRlRjTkJ2S1ZkGkddS1QRcF9mbm1CTGFOVQIsDzY0D15hDF5NDhBJfF0veklaWmhCLlQQWVNnSxgyWB0ODDpQLA5vdBQTFAoOGg8mTlF2S0MgWwFQMRFSNQQgZW0UHz9KWF19SUV0XlZ8AUZDUkQdYUtjYndMVHtRXEBtFxIsLg00CUNUS1RYJRNvYT5WcGhCVUwWQC56S15wTxABCBdaDwo/M35YLSEMNwAiGhhiSU9wFAICFElnJAgmOTFJVCYHAkRgSEJoWE1jAl5fXkIfdFt+dnJOTn5MTV1kVVM0ChUVWhZQVUYdYQI2Ln5CB2RoVUxtWShrWz5wCVIWBRheIgAcNy4fR2o1HAIPFRw5AFpyGFJNFxtCfD03NTcVCHtMGwk6UV5oUlRhGkFeS0YIdUVqZW9aS3xXREJ9QFp2Sw0xQjcDA0kFdUdyPycCR3EfWWZtWVN6MFJhaVJQRw9TLQQxPQ0bFy1fVzskFzE2BAA7BUJPS1RBLhhvACYZDicQRkIjHARyRlBpB0tDV0Mdc1JmeHRPVmhTQVh7V0RvQk9wWhMbIhpVfF9kemMTHjBfRFwwVXl6S0Nwb0NfOlQMYRAwOiwZEQYDGAlwWyQzBSE8WxEGVkUTbUsiOTBHLC0BAQM/Sl00DhR4GUZeUUIfeF1+YnVDVHlbWUx8TEJoRVZnHV5NCRVHBAU2a3RMVmgLERRwSEInR2lwFFJNPEUCHEtvdjgYFicBHiIsFBZnSTQ5WjABCBdacFlwemMKFTtfIwkuDRwoWE0+UQVFSkECdVt8Z3pWTn5aW1V1VVNrX1ZpGkJUTlgRLwokEy0eR3BQWUwkHQtnWlEtGHhNR1QRGlpmC2NHWjMAGQMuEj07BgZtFiUECTZdLgg5Z3BYVmgSGh9wLxY5HwwiB1wDAgMZbF1qZ3JUS35OQF10V0ttR0NhAEReSUEJaEdyOCIMPyYGSFR1VVMzDxttBUEQS34RYUtyDXJPJ2hfVRcvFRw5AC0xWRdQRSNYLyk+OSARS3xAWUw9FgBnPQYzQB0fVFpfJBx6e3tJT3tMR1phTUtoRVtlGFJcU0IIb1plf29aFCkUMAIpREpqR0M5UApQVkBMbWFydmNaIXlUKExwWQg4BwwzXzwMChEMYzw7OAEWFSsJRFlvVVMqBBBtYhcOExtDckU8MzRSV3lWRVx/V0FvR1RkDFxaU1gRcltkZm1NQ2FOVQIsDzY0D15hBUVBRx1VOVZjYz5WcDVof0FgWSQVOS8UFEBnCxtSIAdyBRc7PQ09IiUDJjAcLDwHBlJQRw87YUtydhhIJ2hCSEw2Gx81CAgeVR8IWlZmKAUQOiwZEXlAWUxtCRwpVjU1VwYCFUcfLw4lfm5OS31MQFVhWUZqW01hA15NVkwIb1xhf29aWiYDAykjHU5uR0NwXRYVWkVMbWFydmNaIXs/VUxwWQg4BwwzXzwMChEMYzw7OAEWFSsJR05hWVMqBBBtYhcOExtDckU8MzRSV3xTQUJ7TF96XlNgGkNaS1QFclh8ZHVTVmhCGw07PB0+VlZ8FFIEAwwMcxZ+XGNaWmg5QTFtWU56EAE8WxEGKRVcJFZwASoUOCQNFgd+W196SxM/R087AhdFLhlheC0fDWBPQV58V0doR0NmBEVDXkIdYV1ibm1MT2FOVUwjGAUfBQdtBURBRx1VOVZhK29wWmhCVTd4JFN6VkMrVh4CBB9/IAY3a2EtEyYgGQMuEkd4R0NwRB0eWiJUIh89JHBUFC0VXUF5SEt0WFZ8FERdUFoEc0dybndIVH1QXEBtWR07HSY+UE9fVlgRKA8qa3cHVkJCVUxtIkUHS0NtFAkPCxtSKiUzOyZHWB8LGy4hFhAxXkF8FFIdCAcMFw4xIiwISWYMEBtlVEdoWE1iAF5NUUQEb1NjemNLSH5WW1l0UF96BQImcRwJWkYCbUs7MjtHTzVOf0xtWVMBXD5wFE9NHBZdLgg5GCIXH3VAIgUjOx81CAhmFl5NRwReMlYEMyAOFTpRWwIoDlt3X1JoGkpbS1QHc1p8YHtWWnpWRFljTUVzR0M+VQQoCRAMcl1+dioeAnVUCEBHWVN6SzhoaVJNWlRKIwc9NSg0GyUHSE4aEB0YBwwzX0VPS1QRMQQhaxUfGTwNB19jFxYtQ05kBUVDV0wdYV1gZ21NQmRCR1p4TV1qWUp8FBwMETFfJVZhYW9aEywaSFswVXl6S0Nwb0swR1QMYRAwOiwZEQYDGAlwWyQzBSE8WxEGX1YdYUsiOTBHLC0BAQM/Sl00DhR4GUZfV1oIcEdyYHFLVH5bWUx+SEZsRVppHV5NCRVHBAU2a3BCVmgLERRwQQ52YUNwFFI2VkRsYVZyLSEWFSsJOw0gHE54PAo+dh4CBB8IY0dydjMVCXU0EA85FgFpRQ01Q1pAUkMfc1p+dnVIS2ZaREBtSktiXk1pAltBR1RfIB0XOCdHT3hOVQUpAU5jFk9aFFJNRy8AcDZya2MBGCQNFgcDGB4/VkEHXRwvCxtSKlpidG9aCicRSDooGgc1GVB+WhcaT0UDc1N8YXNWWn5QR0J9SV96WFphAFxZUF0dYQUzIAYUHnVXREBtEBciVlJgSV5nR1QRYTBjZB5aR2gZFwAiGhgUCg41CVA6DhpzLQQxPXJLWGRCBQM+RCU/CBc/RkFDCRFGaVlmZnBUSn9OVVp/T11rW09wB0pUVFoGc0J+di0bDA0MEVF4QV96AgcoCUNcGlg7YUtydhhLSRVCSEw2Gx81CAgeVR8IWlZmKAUQOiwZEXlQV0BtCRwpVjU1VwYCFUcfLw4lfnBITH1MQl9hWUZjW01pAV5NVEwJdUVnYGpWWiYDAykjHU5sXE9wXRYVWkUDPEdYK0lwFicBFABtKicbLCYPYzsjODd3BktvdhAuOw8nKjsENywZLSQPY0NnbRheIgo+diUPFCsWHAMjWRQ/HzAkVRUIJQ1/NAZ6OGpwWmhCVQoiC1MFRxBwXRxNDgRQKBkhfhAuOw8nJkVtHRxQS0NwFFJNR1RYJ0sheC1aR3VCG0w5ERY0SxE1QAcfCVRCYQ48MklaWmhCEAIpc1N6S0MiUQYYFRoREj8TEQYpIXk/fwkjHXlQBwwzVR5NAQFfIh87OS1aHS0WNwk+DSAuCgQ1HFtnR1QRYQc9NSIWWj8LGx9tRFMuBA0lWRAIFVwZJg4mBTcbDi1KXEVjLho0GEpwWwBNV34RYUtyOiwZGyRCFwk+DVNnSzAEdTUoNC8AHGFydmNaHCcQVTNhClMzBUM5RBMEFQcZEj8TEQYpU2gGGmZtWVN6S0NwFBsLRwNYLxhyaH5aCWYQEB1tDRs/BUMyUQEZR0kRMks3OCdwWmhCVQkjHXl6S0NwRhcZEgZfYQk3JTdwHyYGf2ZgVFO4/++yoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7eNQRk5w1ubvR1RyByxydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtm+fYYU59FJD585alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HErHgBCBdQLUsRMCRaR2gZf0xtWVMcBxpwFFJNR1QRYUtya2McGyQREEBtPx8jOBM1URZNR1QRYVZyZXNKVkJCVUxtMB08Ag05QBcnEhlBYVZyMCIWCS1Of0xtWVMUBAA8XQJNR1QRYUtya2McGyQREEBHWVN6SzAgURcJLxVSKktydmNHWi4DGR8oVVMNCg87ZwIIAhARYUtya2NPSmRoVUxtWT81HCQiVQQEEw0RYUtvdiUbFjsHWWZtWVN6PAwiWBZNR1QRYUtydn5aWB8NBwApWUJ4R2lwFFJNJgFFLjw7OGNaWmhCVVFtHxI2GAZ8FCUECTBULQordmNaWmhfVVxjSl96PAo+YAUIAhpiMQ43MmNHWnpSRVxhc1N6S0MRQQYCMB1fFQogMSYOKTwDEgltRFNoR0NwFF9ARydFIAw3di0PFyoHB0w5FlM8ChE9FFpfSkUEaGFydmNaOz0WGjskFyc7GQQ1QDECEhpFYVZyZm9aWmhPWEx9WU56Ag02XRwEExEdYQQmPiYIDSEREEw+DRwqSwI2QBcfRzoRNgI8JUlaWmhCBgk+Cho1BTQ5WiYMFRNUNUtydn5aSmRCVUxgVFMzBRc1RhwMC1RSLh48IiYIWi4NB0w5ERopSxElWnhNR1QRAB4mOREfGCEQAQRtWU56DQI8RxdBbVQRYUsEOSoeKiQDAQoiCx56VkM2VR4eAlgREQczIiUVCCUtEwo+HAd6VkNkGkdBbVQRYUsfOS0JDi0QMD8dWVN6VkM2VR4eAlg7YUtydgcfFi0WECMvCgc7CA81R1JQRxJQLRg3eklaWmhCOwMZHAsuHhE1FFJNR0kRJwo+JSZWcGhCVUwMDAc1PAI8XzEEFRddJEtvdiUbFjsHWUwaGB8xKAoiVx4INRVVKB4hdn5aS31OVTssFRgZAhEzWBc+FxFUJUtvdnBWcGhCVUw+HAApAgw+YxsDFFQRfEtiemMJHzsRHAMjKgc7GRdwCVICFFpFKAY3fmpWcDVof0FgWZHO54HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z6Xl3RkOyoPBNRzJ9GEsBDxAuPwVCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUyv7fFQRk5w1ub5heCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffIPh4CBBVdYS0+LwEsVmgkGRUPPl96LQ8pdx0DCX5dLggzOmM8FjE2GgsqFRYIDgVaPh4CBBVdYQ0nOCAOEycMVT85GAEuLQ8pHFtnR1QRYQc9NSIWWjoNGhhwHhYuOQw/QFpEXFRdLggzOmMSDyVfEgk5MQY3Q0paFFJNRx1XYQU9ImMIFScWVQM/WR01H0M4QR9NExxUL0sgMzcPCCZCEAIpc1N6S0M5UlIrCw1zF0smPiYUWg4ODC4bQzc/GBciWwtFTlRULw9YdmNaWiEEVSohADEdSxc4URxNIRhIAyxoEiYJDjoNDERkWRY0D2lwFFJNDhIRBwcrFSwUFGgWHQkjWTU2EiA/WhxXIx1CIgQ8OCYZDmBLVQkjHXl6S0NwXAcASSRdIB80OTEXKTwDGwhtRFMuGRY1PlJNR1R3LRIQEWNHWgEMBhgsFxA/RQ01Q1pPJRtVOCwrJCxYU0JCVUxtPx8jKSR+eRMVMxtDMB43dn5aLC0BAQM/Sl00DhR4DRdUS01UeEdrM3pTcGhCVUwLFQoYLE0AFFJNR1QRYUtya2NPH3xoVUxtWTU2EiEXGjErFRVcJEtydmNHWjoNGhhjOjUoCg41PlJNR1R3LRIQEW0qGzoHGxhtWVN6VkMiWx0ZbVQRYUsUOjo4LGhfVSUjCgc7BQA1GhwIEFwTAwQ2LxUfFicBHBg0W1pQS0NwFDQBHjZnbyYzLgUVCCsHVUxwWSU/CBc/RkFDCRFGaVI3b29DH3FOTAl0UHl6S0Nwch4UJSIfFw4+OSATDjFCVVFtLxY5HwwiB1wXAgZeS0tydmM8FjEgI0IdGAE/BRdwFFJNWlRDLgQmXGNaWmgkGRUOFh00S15wZgcDNBFDNwIxM20oHyYGEB4eDRYqGwY0DjECCRpUIh96MDYUGTwLGgJlUHl6S0NwFFJNRx1XYQU9ImM5HC9MMwA0WQcyDg1wRhcZEgZfYQ48MklaWmhCVUxtWR81CAI8FBEMCklyIAY3JCJUOQ4QFAEoQlM2BAAxWFIeFxAMAg01eAUWAxsSEAkpQlM2BAAxWFIbAhgMFw4xIiwISWYYEB4ic1N6S0NwFFJNDhIRFBg3JAoUCj0WJgk/Dxo5DlkZRzkIHjBeNgV6Ey0PF2YpEBUOFhc/RTR5FFJNR1QRYUtydmMOEi0MVRooFVhnCAI9Gj4CCB9nJAgmOTFaUDsSEUwoFxdQS0NwFFJNR1RYJ0sHJSYIMyYSABgeHAEsAgA1DjseLBFIBQQlOGs/FD0PWycoADA1DwZ+Z1tNR1QRYUtydmNaWjwKEAJtDxY2Rl4zVR9DKxteKj03NTcVCGhIBhwpWRY0D2lwFFJNR1QRYQI0dhYJHzorGxw4DSA/GRU5VxdXLgd6JBIWOTQUUg0MAAFjMhYjKAw0UVwsTlQRYUtydmNaWmhCAQQoF1MsDg99CREMClpjKAw6IhUfGTwNB0Y+CRd6Dg00PlJNR1QRYUtyPyVaLzsHByUjCQYuOAYiQhsOAk54MiA3LwcVDSZKMAI4FF0RDhoTWxYISTAYYUtydmNaWmhCVUw5ERY0SxU1WFlQBBVcbzk7MSsOLC0BAQM/UwAqD0M1WhZnR1QRYUtydmMTHGg3Bgk/MB0qHhcDUQAbDhdUeyIhHSYDPicVG0QIFwY3RSg1TTECAxEfEhszNSZTWmhCVUxtWQcyDg1wQhcBTElnJAgmOTFJVDEjDQU+WVNwGBM0FBcDA34RYUtydmNaWiEEVTk+HAETBRMlQCEIFQJYIg5oHzAxHzEmGhsjUTY0Hg5+fxcUJBtVJEUeMyUOOScMAR4iFVp6Hws1WlIbAhgcfD03NTcVCHtMDC01EAB6S0kjRBZNAhpVS0tydmNaWmhCMwA0OyV0PQY8WxEEEw0MNw4+bWM8FjEgMkIOPwE7BgZtVxMAbVQRYUs3OCdTcC0MEWZHFRw5Cg9wUgcDBABYLgVyBTcVCg4ODERkc1N6S0MTUhVDIRhIfA0zOjAfcGhCVUwkH1McBxoEWxUKCxFjJA1yIisfFGgSFg0hFVs8Hg0zQBsCCVwYYS0+LxcVHS8OED4oH0kJDhcGVR4YAlxXIAchM2paHyYGXEwoFxdQS0NwFBsLRzJdOCg9OC1aDiAHG0wLFQoZBA0+DjYEFBdeLwU3NTdSU3NCMwA0Ohw0BV4+XR5NAhpVS0tydmMTHGgkGRUPL1N6Sxc4URxNIRhIAz1oEiYJDjoNDERkQlN6S0Nwch4UJSIMLwI+dmNaHyYGf0xtWVMzDUMWWAsvIFQRYR86My1aPCQbNyt3PRYpHxE/TVpEXFQRYUtyEC8DOA9fGwUhWVN6Dg00PlJNR1RdLggzOmMSDyVfEgk5MQY3Q0paFFJNRx1XYQMnO2MOEi0MVQQ4FF0KBwIkUh0fCidFIAU2ayUbFjsHTkwlDB5gKAsxWhUINABQNQ56Ey0PF2YqAAEsFxwzDzAkVQYIMw1BJEUAIy0UEyYFXEwoFxdQDg00PnhASlTT1eewwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8+Q7bEZytNf4WmgsOi8BMCN6QxciVQQIC1QaYR89MSQWH2FCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNheCzS0Z/dqHu7qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnGzkkWFSsDGUwjFhA2AhMTWxwDbRheIgo+diUPFCsWHAMjWRY0CgE8UTwCBBhYMUN7XGNaWmgLE0wjFhA2AhMTWxwDRwBZJAVyOCwZFiESNgMjF0keAhAzWxwDAhdFaUJyMy0ecGhCVUwjFhA2AhMTWxwDR0kREx48BSYIDCEBEEIeDRYqGwY0DjECCRpUIh96MDYUGTwLGgJlUHl6S0NwFFJNRxheIgo+diBHHS0WNgQsC1tzUEM5UlIDCAARIksmPiYUWjoHARk/F1M/BQdaFFJNR1QRYUs0OTFaJWQSVQUjWRoqCgoiR1oOXTNUNS83JSAfFCwDGxg+UVpzSwc/PlJNR1QRYUtydmNaWiEEVRx3MAAbQ0ESVQEINxVDNUl7djcSHyZCBUIOGB0ZBA88XRYIWhJQLRg3diYUHkJCVUxtWVN6SwY+UHhNR1QRJAU2f0kfFCxoGQMuGB96DRY+VwYECBoRJQIhNyEWHwYNFgAkCVtzYUNwFFIEAVRfLgg+PzM5FSYMVRglHB16BQwzWBsdJBtfL1EWPzAZFSYMEA85UVphSw0/Vx4EFzdeLwVvOCoWWi0MEWYoFxdQYU59FJD565alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEpHhASlTT1elydhU1MwxCJSAMLTUVOS5w1vL5RydeLQI2dgIUGSANBwkpWT0/BA1wdh4CBB8RYUtydmNaWmhCVUxtWVN6S0NwFJD55X4cbEuwwteY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1fNYOiwZGyRCAwMkHSM2Chc2WwAAbX5dLggzOmMcDyYBAQUiF1MoDg4/Qhc7CB1VEQczIiUVCCVKXGZtWVN6AgVwQh0EAyRdIB80OTEXWjwKEAJtDxwzDzM8VQYLCAZcey83JTcIFTFKXFdtDxwzDzM8VQYLCAZcYVZyOCoWWi0MEWYoFxdQYQ8/VxMBRxJELwgmPywUWisQEA05HCU1AgcAWBMZARtDLEN7XGNaWmgQEAEiDxYMBAo0ZB4MExJeMwZ6f0laWmhCGQMuGB96GQw/QFJQRxNUNTk9OTdSU3NCHAptFxwuSxE/WwZNExxUL0sgMzcPCCZCEAIpc3l6S0NwWB0OBhgRMUtvdgoUCTwDGw8oVx0/HEtyZBMfE1YYS0tydmMKVAYDGAltWVN6S0NwFFJNWlQTFwQ7MhMWGzwEGh4gW3l6S0NwRFw+Dg5UYUtydmNaWmhCVVFtLxY5HwwiB1wDAgMZdV5+dnJUSGRCQVlkc1N6S0MgGjMDBBxeMw42dmNaWmhCSEw5CwY/YUNwFFIdSTdQLyg9Oi8THi1CVUxtRFMuGRY1PlJNR1RBbygzOBcVDysKVUxtWVN6VkM2VR4eAn4RYUtyJm0uCCkMBhwsCxY0CBpwFE9NV1oFdGFydmNaCmYgBwUuEjA1BwwiFFJNR0kRAxk7NSg5FSQNB0IjHARySSApVRxPTn4RYUtyJm03GzwHBwUsFVN6S0NwFE9NIhpELEUfNzcfCCEDGUIDHBw0YUNwFFIdSTdQMh8BPiIeFT9CVUxtRFM8Cg8jUXhNR1QRMUUREDEbFy1CVUxtWVN6S15wdzQfBhlUbwU3IWsIFScWWzwiChouAgw+GipBRwZeLh98BiwJEzwLGgJjIFN3SyA2U1w9CxVFJwQgOwwcHDsHAUBtCxw1H00AWwEEEx1eL0UIf0laWmhCBUIdGAE/BRdwFFJNR1QRYVZyISwIETsSFA8oc3l6S0NwQh0EAyRdIB80OTEXWnVCBWYoFxdQYTElWiEIFQJYIg58HiYbCDwAEA05QzA1BQ01VwZFAQFfIh87OS1SU0JCVUxtEBV6BQwkFDELAFpnLgI2Bi8bDi4NBwFtDRs/BUMiUQYYFRoRJAU2XGNaWmgOGg8sFVMoBAwkFE9NABFFEwQ9ImtTQWgLE0wjFgd6GQw/QFIZDxFfYRk3IjYIFGgHGwhHWVN6Swo2FBwCE1RHLgI2Bi8bDi4NBwFtFgF6BQwkFAQCDhBhLQomMCwIF2YyFB4oFwd6Hws1WnhNR1QRYUtydiAIHykWEDoiEBcKBwIkUh0fClwYeksgMzcPCCZoVUxtWRY0D2lwFFJNERtYJTs+NzccFToPWy8LCxI3DkNtFDErFRVcJEU8MzRSCCcNAUIdFgAzHwo/Wlw1S1RDLgQmeBMVCSEWHAMjVyp6RkMTUhVDNxhQNQ09JC41HC4REBhhWQE1BBd+ZB0eDgBYLgV8DGpwHyYGXGZHVF56iffc1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+fKYU59FJD55VQRDCQcBRc/KGgnJjxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtm+fYYU59FJD585alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HErHgBCBdQLUs3JTM9DyERVUxtWVN6S15wTw9nCxtSIAdyOywUCTwHBy0pHRY+KAw+WnhnCxtSIAdyMDYUGTwLGgJtGh8/ChEVZyJFTn4RYUtyPyVaFycMBhgoCzI+DwY0dx0DCVRFKQ48di4VFDsWEB4MHRc/DyA/WhxXIx1CIgQ8OCYZDmBLTkwgFh0pHwYidRYJAhByLgU8dn5aFCEOVQkjHXl6S0NwUh0fRysdJks7OGMKGyEQBkQoCgMdHgojHVIJCFRBIgo+OmscDyYBAQUiF1tzSwRqcBceEwZeOEN7diYUHmFCEAIpc1N6S0M1RwIqEh1CYVZyLT5wHyYGf2YhFhA7B0M2QRwOEx1eL0szMic/KRg2GiEiHRY2Qw4/UBcBTn4RYUtyPyVaHzsSMhkkCig3BAc1WC9NExxUL0sgMzcPCCZCEAIpc1N6S0M8WxEMC1RDLgQmdn5aFycGEAB3Pxo0DyU5RgEZJBxYLQ96dAsPFykMGgUpKxw1HzMxRgZPTlReM0s/OScfFmYyBwUgGAEjOwIiQHhNR1QRKA1yOCwOWjoNGhhtDRs/BUMiUQYYFRoRJAU2XElaWmhCWEFtKxYpBA8mUVIJDgdBLQordi0bFy1YVRg/AFMSHg4xWh0EA1p1KBgiOiIDNCkPEEyv/+F6Bgw0UR5DKRVcJEuw0NFaWAUNGx85HAF4YUNwFFIBCBdQLUs6Iy5aR2gPGggoFUkcAg00chsfFAByKQI+MgwcOSQDBh9lWzsvBgI+WxsJRV07YUtydi8VGSkOVQAsGxY2S15wFlBnR1QRYRsxNy8WUi4XGw85EBw0Q0paFFJNR1QRYUs7MGMSDyVCFAIpWRsvBk0UXQEdCxVIDwo/M2MbFCxCHRkgVzczGBM8VQsjBhlUYRVvdmFYWjwKEAJHWVN6S0NwFFJNR1QRLQowMy9aR2gKAAFjPRopGw8xTTwMChE7YUtydmNaWmgHGR8oEBV6Bgw0UR5DKRVcJEszOCdaFycGEABjNxI3DkMuCVJPRVRFKQ48XGNaWmhCVUxtWVN6Sw8xVhcBR0kRLAQ2My9UNCkPEGZtWVN6S0NwFBcBFBE7YUtydmNaWmhCVUxtFRI4Dg9wCVJPKhtfMh83JGFwWmhCVUxtWVM/BQdaFFJNRxFfJUJYdmNaWiEEVQAsGxY2S15tFFBPRwBZJAVyOiIYHyRCSExvNBw0GBc1RlBNAhpVS2FydmNaFicBFABtGxF6VkMZWgEZBhpSJEU8MzRSWAoLGQAvFhIoDyQlXVBEbVQRYUswNG00GyUHVUxtWVN6S0NwFFJNWlQTDAQ8JTcfCA0xJU5HWVN6SwEyGiEEHRERYUtydmNaWmhCVUxwWSYeAg5iGhwIEFwBbVpmZm9KVnpaXGZtWVN6CQF+ZwYYAwd+Jw0hMzdaWmhCVVFtLxY5HwwiB1wDAgMZcUdmeHZWSmFoVUxtWRE4RSI8QxMUFDtfFQQidmNaWmhfVRg/DBZQS0NwFBAPSTVVLhk8MyZaWmhCVUxtWVNnSxE/WwZnR1QRYQkweBMbCC0MAUxtWVN6S0NwFFJQRwZeLh9YXGNaWmgOGg8sFVM4DENtFDsDFABQLwg3eC0fDWBAMx4sFBZ4QmlwFFJNBRMfEgIoM2NaWmhCVUxtWVN6S0NwFFJNR1QMYT4WPy5IVCYHAkR8VUN2Wk9gHXhNR1QRIwx8FCIZES8QGhkjHTA1BwwiB1JNR1QRYUtvdgAVFicQRkIrCxw3OSQSHENVS0UJbVpqf0laWmhCFwtjOxI5AAQiWwcDAyBDIAUhJiIIHyYBDExwWUN0WGlwFFJNBRMfAwQgMiYIKSEYEDwkARY2S0NwFFJNR1QMYVtYdmNaWioFWzwsCxY0H0NwFFJNR1QRYUtydmNaWmhCSEwvG3lQS0NwFB4CBBVdYQg9JC0fCGhfVSUjCgc7BQA1GhwIEFwTFCIROTEUHzpAXGZtWVN6CAwiWhcfSTdeMwU3JBEbHiEXBkxwWSYeAg5+WhcaT0QddUJYdmNaWisNBwIoC10KChE1WgZNR1QRYUtya2MYHUJoVUxtWR81CAI8FBwMChF9YVZyHy0JDikMFgljFxYtQ0EEUQoZKxVTJAdwf0laWmhCGw0gHD90OAoqUVJNR1QRYUtydmNaWmhCVUxtWU56Pic5WUBDCRFGaVp+Zm9LVnhLf0xtWVM0Cg41eFwvBhdaJhk9Iy0eLjoDGx89GAE/BQApCVJcbVQRYUs8Ny4fNmY2EBQ5Ohw2BBFjFFJNR1QRYUtydmNaR2ghGgAiC0B0DRE/WSAqJVwDdF5+YXNWTXhLf0xtWVM0Cg41eFw5AgxFEggzOiYeWmhCVUxtWVN6S0NwCVIZFQFUS0tydmMUGyUHOUILFh0uS0NwFFJNR1QRYUtydmNaWmhCSEwIFwY3RSU/WgZDIBtFKQo/FCwWHkJCVUxtFxI3Di9+YBcVE1QRYUtydmNaWmhCVUxtWVN6S15wWBMPAhg7YUtydi0bFy0uWzwsCxY0H0NwFFJNR1QRYUtydmNaWmhfVQ4qc3l6S0NwUQEdIAFYMjA/OScfFhVCSEwvG3k/BQdaPh4CBBVdYQ0nOCAOEycMVR8oDQYqJgw+RwYIFTFiESc7JTcfFC0QXUVHWVN6Swo2FB8CCQdFJBkTMicfHgsNGwJtDRs/BUM9WxweExFDAA82Myc5FSYMTygkChA1BQ01VwZFTlRULw9YdmNaWiUNGx85HAEbDwc1UDECCRoRfEslOTERCTgDFgljPRYpCAY+UBMDEzVVJQ42bAAVFCYHFhhlHwY0CBc5WxxFCBZbaGFydmNaWmhCVQUrWR01H0MTUhVDKhtfMh83JAYpKmgWHQkjWQE/HxYiWlIICRA7YUtydmNaWmgWFB8mVwQ7Ahd4BFxYTn4RYUtydmNaWiEEVQMvE0kTGCJ4Fj8CAxFdY0JyNy0eWiYNAUwkCiM2Cho1RjEFBgYZLgk4f2MOEi0Mf0xtWVN6S0NwFFJNRxheIgo+disPF2hfVQMvE0kcAg00chsfFAByKQI+MgwcOSQDBh9lWzsvBgI+WxsJRV07YUtydmNaWmhCVUxtEBV6AxY9FBMDA1RZNAZ8GyICMi0DGRglWU16W0MkXBcDbVQRYUtydmNaWmhCVUxtWVM7DwcVZyI5CDleJQ4+fiwYEGFoVUxtWVN6S0NwFFJNAhpVS0tydmNaWmhCEAIpc1N6S0M1WhZEbRFfJWFYOiwZGyRCExkjGgczBA1wRhcLFRFCKSY9ODAOHzonJjxlUHl6S0NwVx4IBgZ0Ejt6f0laWmhCHAptFxwuSyA2U1wgCBpCNQ4gExAqWjwKEAJtCxYuHhE+FBcDA34RYUtyMCwIWhdOGg4nWRo0SwogVRsfFFxGLhk5JTMbGS1YMgk5PRYpCAY+UBMDEwcZaEJyMixwWmhCVUxtWVMzDUM/VhhXLgdwaUkfOScfFmpLVQ0jHVM0BBdwXQE9CxVIJBkRPiIIUicAH0VtDRs/BWlwFFJNR1QRYUtydmMWFSsDGUwlDB56VkM/VhhXIR1fJS07JDAOOSALGQgCHzA2ChAjHFAlEhlQLwQ7MmFTcGhCVUxtWVN6S0NwFBsLRxxELEszOCdaEj0PWyEsATs/Cg8kXFJTR0QRNQM3OElaWmhCVUxtWVN6S0NwFFJNBhBVBDgCAiw3FSwHGUQiGxlzYUNwFFJNR1QRYUtydiYUHkJCVUxtWVN6SwY+UHhNR1QRJAU2XGNaWmgREBg4CT41BRAkUQAoNCR9KBgmMy0fCGBLfwkjHXlQRk5w1ubhheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffAPl9AR5alw0tyEgY2PxwnVSMPKicbKC8VZ1JFCxVHIEt9digTFiRCWkwlGAk7GQdwVgsdBgdCaEtydmNaWmhCVUxtWVN6S4HEtnhASlTT1f+wwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8+w7LQQxNy9aFSoRAQ0uFRYeAhAxVh4IAyRQMx8hdn5aATVofwAiGhI2SywSZyYsJDh0HiAXDxQ1KAwxVVFtAlE2ChUxFl5PDB1dLUl+dCsbACkQEU5hWxI5AgdyGFAdCB1CLgVwemEJCiEJEE5hWxc/Chc4Fl5PERtYJUl+dCUTCC1AWU4vDAE0SU9yQB0VDhcTPGFYOiwZGyRCExkjGgczBA1wXQEiBQdFIAg+MxMbCDxKBQ0/DVpQS0NwFBsLRxpeNUsiNzEOQAERNERvOxIpDjMxRgZPTlRFKQ48djEfDj0QG0wrGB8pDkM1WhZnR1QRYQc9NSIWWiZCSEw9GAEuRS0xWRdXCxtGJBl6f0laWmhCEwM/WSx2ABRwXRxNDgRQKBkhfgw4KRwjNiAIJjgfMjQfZjY+TlRVLmFydmNaWmhCVQUrWR1gDQo+UFoGEF0RNQM3OGMIHzwXBwJtDQEvDkM1WhZnR1QRYQ48MklaWmhCWEFtOB8pBEMzXBcODFRBIBk3ODdaFCkPEGZtWVN6AgVwRBMfE1phIBk3ODdaDiAHG2ZtWVN6S0NwFB4CBBVdYRs8dn5aCikQAUIdGAE/BRd+ehMAAk5dLhw3JGtTcGhCVUxtWVN6DQwiFC1BDAMRKAVyPzMbEzoRXSMPKicbKC8VazkoPiN+Ey8Bf2MeFUJCVUxtWVN6S0NwFFIEAVRBL1E0Py0eUiMVXEw5ERY0SxE1QAcfCVRFMx43diYUHkJCVUxtWVN6SwY+UHhNR1QRJAU2XGNaWmgQEBg4Cx16DQI8RxdnAhpVS2E+OSAbFmgEAAIuDRo1BUM0XQEMBRhUFgQgOidILjoDBR9lUHl6S0NwRBEMCxgZJx48NTcTFSZKXGZtWVN6S0NwFB4CBBVdYRxgdn5aDScQHh89GBA/USU5WhYrDgZCNSg6Py8eUmo1Oj4BPVNoSUpaFFJNR1QRYUs7MGMNSGgWHQkjc1N6S0NwFFJNR1QRYUZ/dgcfFi0WEEwsFR96GBcxUxdAFARUIgI0PyBaFSoRAQ0uFRYpYUNwFFJNR1QRYUtydiUVCGg9WUw+DRI9DkM5WlIEFxVYMxh6IXFAPS0WNgQkFRcoDg14HVtNAxs7YUtydmNaWmhCVUxtWVN6Swo2FAEZBhNUbyUzOyZAHCEMEURvKgc7DAZyHVIZDxFfS0tydmNaWmhCVUxtWVN6S0NwFFJNSlkRBQ4+MzcfWikOGUwgFgUzBQRwQxMBCwcdYQ89OTEJVmgDGwhtFhEpHwIzWBcebVQRYUtydmNaWmhCVUxtWVN6S0NwUh0fRysdYQQwPGMTFGgLBQ0kCwByGBcxUxdXIBFFBQ4hNSYUHikMAR9lUFp6DwxaFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwWB0OBhgRLwo/M2NHWicAH0IDGB4/UQ8/QxcfT107YUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRKA1yOCIXH3IEHAIpUVEtCg88FltNCAYRLwo/M3kcEyYGXU4pFhwoSUpwWwBNCRVcJFE0Py0eUmoPGhokFxR4QkM/RlIDBhlUew07OCdSWDwQFBxvUFM1GUM+VR8IXRJYLw96dCgTFiRAXEwiC1M0Cg41DhQECRAZYxgiPygfWGFCGh5tFxI3Dlk2XRwJT1ZdIB0zdGpaDiAHG2ZtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6GwAxWB5FAQFfIh87OS1SU2gNFwZ3PRYpHxE/TVpERxFfJUJYdmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtyMy0ecGhCVUxtWVN6S0NwFFJNR1QRYUtyMy0ecGhCVUxtWVN6S0NwFFJNR1RULw9YdmNaWmhCVUxtWVN6Dg00PlJNR1QRYUtydmNaWkJCVUxtWVN6S0NwFFJASlR1JAc3IiZaGyQOVSIdOgB6Ag1wYx0fCxARc2FydmNaWmhCVUxtWVM8BBFwa15NCBZbYQI8dioKGyEQBkQ6S0kdDhcUUQEOAhpVIAUmJWtTU2gGGmZtWVN6S0NwFFJNR1QRYUtyPyVaFSoITyU+OFt4Jgw0UR5PTlRQLw9yfiwYEGYsFAEoQx81HAYiHFtXAR1fJUNwODMZWGFCGh5tFhEwRS0xWRdXCxtGJBl6f3kcEyYGXU4oFxY3EkF5FB0fRxtTK0UcNy4fQCQNAgk/UVpgDQo+UFpPChtfMh83JGFTU2gWHQkjc1N6S0NwFFJNR1QRYUtydmNaWmhCBQ8sFR9yDRY+VwYECBoZaEs9NClAPi0RAR4iAFtzSwY+UFtnR1QRYUtydmNaWmhCVUxtWRY0D2lwFFJNR1QRYUtydmMfFCxoVUxtWVN6S0M1WhZnR1QRYUtydmNwWmhCVUxtWVN3RkMUUR4IExERIAc+diwYCTwDFgAoClMzBUMAXRcKAgcRZ0seNzUbcGhCVUxtWVN6BwwzVR5NFxgRfEslOTERCTgDFgl3Pxo0DyU5RgEZJBxYLQ96dBMTHy8HBkxrWT87HQJyHXhNR1QRYUtydiocWjgOVRglHB1QS0NwFFJNR1QRYUtyMCwIWhdOVQMvE1MzBUM5RBMEFQcZMQdoESYOPi0RFgkjHRI0HxB4HVtNAxs7YUtydmNaWmhCVUxtWVN6Sw8/VxMBRxpQLA5ya2MVGCJMOw0gHEk2BBQ1RlpEbVQRYUtydmNaWmhCVUxtWVMzDUM+VR8IXRJYLw96dC8bDClAXEwiC1M0Cg41DhQECRAZYx8gNzNYU2gNB0wjGB4/UQU5WhZFRR9YLQdwf2MVCGgMFAEoQxUzBQd4FgEdDh9UY0JyOTFaFCkPEFYrEB0+Q0E4VQgMFRATaEsmPiYUcGhCVUxtWVN6S0NwFFJNR1QRYUtyJiAbFiRKExkjGgczBA14HVICBR4LBQ4hIjEVA2BLVQkjHVpQS0NwFFJNR1QRYUtydmNaWi0MEWZtWVN6S0NwFFJNR1RULw9YdmNaWmhCVUwoFxdQS0NwFFJNR1Q7YUtydmNaWmhPWEwJHB8/HwZwVR4BRzphAhhyPy1aDScQHh89GBA/YUNwFFJNR1QRJwQgdhxWWicAH0wkF1MzGwI5RgFFEBtDKhgiNyAfQA8HASgoChA/BQcxWgYeT10YYQ89XGNaWmhCVUxtWVN6Swo2FB0PDU54Mip6dA4VHi0OV0VtGB0+S0s/VhhDKRVcJFE+OTQfCGBLTwokFxdySQ0gV1BERxtDYQQwPG00GyUHTwAiDhYoQ0pqUhsDA1wTJAU3OzpYU2gNB0wiGxl0JQI9UUgBCANUM0N7bCUTFCxKVwEiFwAuDhFyHVtNExxUL2FydmNaWmhCVUxtWVN6S0NwRBEMCxgZJx48NTcTFSZKXEwiGxlgLwYjQAACHlwYYQ48MmpwWmhCVUxtWVN6S0NwURwJbVQRYUtydmNaHyYGf0xtWVM/BQd5PhcDA347LQQxNy9aHD0MFhgkFh16ChMgWAspAhhUNQ4dNDAOGysOEB9lUHl6S0NwWB0OBhgRIgQnODdaR2hSf0xtWVMzDUMTUhVDMBtDLQ9ya35aWB8NBwApWUF4Sxc4URxNAx1CIAk+MxQVCCQGRzg/GAMpQ0pwURwJbVQRYUs0OTFaJWQSFB45WRo0SwogVRsfFFxGLhk5JTMbGS1YMgk5PRYpCAY+UBMDEwcZaEJyMixwWmhCVUxtWVMzDUM5Rz0PFABQIgc3BiIIDmASFB45UFMuAwY+PlJNR1QRYUtydmNaWjgBFAAhURUvBQAkXR0DT107YUtydmNaWmhCVUxtWVN6Swo2FBwCE1ReIxgmNyAWHwwLBg0vFRY+OwIiQAE2FxVDNTZyIisfFEJCVUxtWVN6S0NwFFJNR1QRYUtydiwYCTwDFgAoPRopCgE8URY9BgZFMjAiNzEOJ2hfVRcOGB0OBBYzXE8dBgZFbygzOBcVDysKWUwOGB0ZBA88XRYIWgRQMx98FSIUOScOGQUpHF96PxExWgEdBgZULwgrazMbCDxMIR4sFwAqChE1WhEUGn4RYUtydmNaWmhCVUxtWVN6Dg00PlJNR1QRYUtydmNaWmhCVUw9GAEuRSAxWiYCEhdZYUtydmNaR2gEFAA+HHl6S0NwFFJNR1QRYUtydmNaCikQAUIOGB0ZBA88XRYIR1QRYVZyMCIWCS1oVUxtWVN6S0NwFFJNR1QRYRszJDdULjoDGx89GAE/BQApFFJQR0Qfdl5YdmNaWmhCVUxtWVN6S0NwFBECEhpFYVZyNSwPFDxCXkx8c1N6S0NwFFJNR1QRYQ48MmpwWmhCVUxtWVM/BQdaFFJNRxFfJWFydmNaCC0WAB4jWRA1Hg0kPhcDA347LQQxNy9aHD0MFhgkFh16GQYjQB0fAjtTMh8zNS8fCWBLf0xtWVM8BBFwRBMfE1hCIB03MmMTFGgSFAU/Cls1CRAkVREBAjBYMgowOiYeKikQAR9kWRc1YUNwFFJNR1QRMQgzOi9SHD0MFhgkFh1yQmlwFFJNR1QRYUtydmMKGzoWWy8sFyc1HgA4FFJNWlRCIB03Mm05GyY2GhkuEXl6S0NwFFJNR1QRYUsiNzEOVAsDGy8iFR8zDwZwCVIeBgJUJUURNy05FSQOHAgoc1N6S0NwFFJNR1QRYRszJDdULjoDGx89GAE/BQApFE9NFBVHJA98AjEbFDsSFB4oFxAjYUNwFFJNR1QRJAU2f0laWmhCEAIpc1N6S0M/VgEZBhddJC87JSIYFi0GJQ0/DQB6VkMrSXgICRA7S0Z/dgAVFDwLGxkiDAB6BAEjQBMOCxERNgomNSsfCGhKFg05Ghs/GEM+UQUBHlRdLgo2MydaCikQAR9kcwc7GAh+RwIMEBoZJx48NTcTFSZKXGZtWVN6HAs5WBdNEwZEJEs2OUlaWmhCVUxtWQc7GAh+QxMEE1wBb157XGNaWmhCVUxtEBV6KAU3GjYICxFFJCQwJTcbGSQHBkw5ERY0YUNwFFJNR1QRYUtydjMZGyQOXQ09CR8jLwY8UQYIKBZCNQoxOiYJU0JCVUxtWVN6SwY+UHhNR1QRJAU2XCYUHmFofxsiCxgpGwIzUVwpAgdSJAU2Ny0OOywGEAh3Ohw0BQYzQFoLEhpSNQI9OGsVGCJLf0xtWVMzDUM+WwZNJBJWby83OiYOHwcABhgsGh8/GEMkXBcDRwZUNR4gOGMfFCxoVUxtWQc7GAh+QxMEE1wBb1p7XGNaWmgLE0wkCjw4GBcxVx4INxVDNUM9NClTWjwKEAJHWVN6S0NwFFIdBBVdLUM0Iy0ZDiENG0Rkc1N6S0NwFFJNR1QRYQQwPG05GyY2GhkuEVN6S15wUhMBFBE7YUtydmNaWmhCVUxtFhEwRSAxWjECCxhYJQ5ya2McGyQREGZtWVN6S0NwFFJNR1ReIwF8AjEbFDsSFB4oFxAjS15wBFxaUn4RYUtydmNaWi0MEUVHWVN6SwY+UHgICRAYS2F/e2OY7sSA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwsOY7siA4eyv7fO4/+OyoPKP8/TT1euwwtNwV2VCl/jPWVMUJEMEcSo5MiZ0YUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtytNf4cGVPVY7Z7ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr27WYhFhA7B0MjVQQIAyBUOR8nJCYJWnVCDhFHcx81CAI8FBQYCRdFKAQ8diIKCiQbOwMZHAsuHhE1HFtnR1QRYQ09JGMlVicAH0wkF1MzGwI5RgFFEBtDKhgiNyAfQA8HASgoChA/BQcxWgYeT10YYQ89XGNaWmhCVUxtCRA7Bw94UgcDBABYLgV6f0laWmhCVUxtWVN6S0M5UlICBR4LCBgTfmEuHzAWAB4oW1p6BBFwWxAHXT1CAENwEiYZGyRAXEw5ERY0YUNwFFJNR1QRYUtydmNaWmgRFBooHSc/ExclRhcePBtTKzZya2MVGCJMIR4sFwAqChE1WhEUbVQRYUtydmNaWmhCVUxtWVM1CQl+YAAMCQdBIBk3OCADWnVCRGZtWVN6S0NwFFJNR1RULRg3PyVaFSoITyU+OFt4OBM1VxsMCzlUMgNwf2MVCGgNFwZ3MAAbQ0ESWB0ODDlUMgNwf2MOEi0Mf0xtWVN6S0NwFFJNR1QRYUshNzUfHhwHDRg4CxYpMAwyXi9NWlReIwF8AiYCDj0QECUpc1N6S0NwFFJNR1QRYUtydmMVGCJMIQk1DQYoDio0FE9NRVY7YUtydmNaWmhCVUxtHB8pDgo2FB0PDU54Mip6dAEbCS0yFB45W1p6Cg00FBwCE1ReIwFoHzA7Umo3GwUiFzwqDhExQBsCCVYYYR86My1wWmhCVUxtWVN6S0NwFFJNRwdQNw42AiYCDj0QEB8WFhEwNkNtFB0PDVp8IB83JCobFkJCVUxtWVN6S0NwFFJNR1QRLgk4eA4bDi0QHA0hWU56Lg0lWVwgBgBUMwIzOm0pFycNAQQdFRIpHwozPlJNR1QRYUtydmNaWi0MEWZtWVN6S0NwFBcDA107YUtydiYUHkIHGwhHcx81CAI8FBQYCRdFKAQ8djEfCTwNBwkZHAsuHhE1R1pEbVQRYUs0OTFaFSoIWRosFVMzBUMgVRsfFFxCIB03MhcfAjwXBwk+UFM+BGlwFFJNR1QRYRsxNy8WUi4XGw85EBw0Q0paFFJNR1QRYUtydmNaEy5CGg4nQzopKktyYBcVEwFDJEl7diwIWicAH1YECjJySSc1VxMBRV0RNQM3OElaWmhCVUxtWVN6S0NwFFJNCBZbbz8gNy0JCikQEAIuAFNnSxUxWHhNR1QRYUtydmNaWmgHGR8oEBV6BAE6DjseJlwTEhs3NSobFgUHBgRvUFM1GUM/VhhXLgdwaUkQOiwZEQUHBgRvUFMuAwY+PlJNR1QRYUtydmNaWmhCVUwiGxl0PwYoQAcfAj1VYVZyICIWcGhCVUxtWVN6S0NwFBcBFBFYJ0s9NClAMzsjXU4PGAA/OwIiQFBERwBZJAVYdmNaWmhCVUxtWVN6S0NwFB0PDVp8IB83JCobFmhfVRosFXl6S0NwFFJNR1QRYUs3OCdwWmhCVUxtWVM/BQd5PlJNR1RULw9YdmNaWjsDAwkpLRYiHxYiUQFNWlRKPGE3OCdwcGVPVY7Z9ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr25WZgVFO4/+FwFDU/KCF/BUYUGQ82NR8rOyttLSQfLi1wFFobUloIaEtydmNaWmhCVUxtWVN6S0NwFFJNR1QRYUtydmNaWmiA4e5HVF56iffSFFKP59YREh89JjBaPCQbVQokCwAuSxA/FDACAw1nJAc9NSoOA2gBFAJqDVM8AgQ4QFIZDxERLAQkMy4fFDxCVUyv7fFQRk5w1ubvR1TTwclyBCIDGSkRAR9tPTwNJUM1QhcfHlRPcF5yJTcPHjtCAQNtHxo0D0M7UQsOBgQRMh4gMCIZH2hCVUxtWVO4/+FaGV9NheCzYUuw1uFaLzsHBkwfHB0+DhEDQBcdFxFVYQc9OTNamMjxVR8oDQB6KCUiVR8IRxFHJBkrdiUIGyUHVR8iWVN6S0NwFJD55X4cbEuwwsFaWmhCBQQ0Cho5GEMTdTwjKCARLh03JDETHi1CHBhtWVN6S0NwFFJNR1QRYUtydmNaWmhCVUxtWVN6S0NwFFJNheCzS0Z/dqHu+GhCl+zvWT01CA85RFIiKVRCLks9NDAOGysOEB9tHRw0TBdwVh4CBB8RNQM3djMbDiBCVUxtWVN6S0NwFFJNR1QRo//QXG5XWqr24Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu+qr29Y7Z+ZHO64HEtJD555alwYnG1qHu4kJoGQMuGB96LDEfYTwpOCZwGDQCFxE7NxtCSEwfGAo5ChAkZBMfBhlCbwU3IWtTcA8wOjkDPSwIKjoPZDM/Jjliby07OjcfCBwbBQltRFMfBRY9GiAMHhdQMh8UPy8OHzo2DBwoVzYiCA8lUBdnbRheIgo+diUPFCsWHAMjWQYqDwIkUSAMHjFJIgcnJSoVFGBLf0xtWVM2BAAxWFIOR0kRJg4mFSsbCGBLf0xtWVMdOSwFejYyNTVoHjsTBAI3KWYkHAA5HAEeDhAzURwJBhpFMiI8JTcbFCsHBkxwWRB6Cg00FAkOGlReM0spK0kfFCxof0FgWTEvAg80FBNNCx1CNUs9MGMNGzESGgUjDQB6HAokXFIJDgZUIh9yPy0OHzoSGgAsDRo1BUN4Wh1NFRVIIgohIioUHWFoWEFtMB0uDhEgWx4MExFCYTJyJjEVCi0QGRVtChx6Hws1FBEFBgZQIh83JGMcFSQOGhs+WQE7BhMjFBMDA1RCLQQiMzBwFicBFABtHwY0CBc5WxxNBQFYLQ8VJCwPFCw1FBU9Fho0HxB4RwYMFQBhLhh+djcbCC8HATwiClpQS0NwFB4CBBVdYRwzLzMVEyYWBkxwWQgnYUNwFFIBCBdQLUs2LmNHWjwDBwsoDSM1GE0IFF9NFABQMx8COTBUIkJCVUxtFRw5Cg9wUAhNWlRFIBk1MzcqFTtML0xgWQAuChEkZB0eSS47YUtydi8VGSkOVQg0WU56HwIiUxcZNxtCbzJye2MJDikQATwiCl0DYUNwFFIBCBdQLUsmOTcbFgwLBhhtRFM3Chc4GgEcFQAZJRNyfGMeAmhJVQg3WVl6DxlwH1IJHlQbYQ8rf0laWmhCGQMuGB96ODcVZFJNWlQDcUtydm5XWjsDGBwhHFM/HQYiTVJfV1RCNR42JUlaWmhCGQMuGB96BTAkUQIeR0kRLAomPm0XGzBKR0BtFBIuA00zURsBTwBeNQo+EioJDmhNVT8ZPCNzQmlwFFJNbVQRYUs0OTFaE2hfVVxhWR0JHwYgR1IJCH4RYUtydmNaWiQNFg0hWQd6VkM5FF1NCSdFJBshXGNaWmhCVUxtFRw5Cg9wQwpNWlRCNQogIhMVCWY6VUdtHQt6QUMkPlJNR1QRYUtyOiwZGyRCAhVtRFMpHwIiQCICFFpoYUByMjpaUGgWVUxgVFMTBRc1RgICCxVFJEsLdjAVWj8HVQoiFR81HEMjWB0dAgc7YUtydmNaWmgOGg8sFVMtEUNtFAEZBgZFEQQheBlaUWgGD0xnWQdQS0NwFFJNR1RFIAk+M20TFDsHBxhlDhIjGww5WgYeS1RnJAgmOTFJVCYHAkQ6AV96HBp8FAUXTl07YUtydiYUHkJCVUxtVF56LQwiVxdNAgxQIh9yMiYJDiEMFBgkFh16ChBwUhsDBhgRNgorJiwTFDxoVUxtWQQ7EhM/XRwZFC8SNgorJiwTFDwRKExwWQc7GQQ1QCICFH4RYUtyJCYODzoMVRssAAM1Ag0kR3gICRA7S0Z/dg4VDC1CAQQoWRAyChExVwYIFVRFKRk9IyQSWilCBgUjHh8/SxA1Ux8ICQARNBg7OCRaG2gRGAMiDRt6PxQ1URw+AgZHKAg3djcNHy0MW2ZgVFMNDkMkQxcICVRQYSgUJCIXHx4DGRkoWRI0D0MxRAIBHlRYNUs3ICYIA2gEBw0gHF96DAomXRwKRxURJwcnPydaHSQLEQltEB0pHwYxUFICAVRQYRg8NzNUcGVPVQgsFxQ/GSA4UREGXVReMR87OS0bFmgEAAIuDRo1BUt5FF9TRxZeLgc3Ny1WWiEEVR4oDQYoBRBwQAAYAlRFNg43OGMTCWgBFAIuHB82DgdwXR8AAhBYIB83OjpwFicBFABtHwY0CBc5WxxNChtHJDg3MS4fFDxKBgkqPwE1Bk9wRxcKMxsdYRgiMyYeVmgGFAIqHAEZAwYzX1tnR1QRYQc9NSIWWiwLBhhtRFNyGAY3YB1NSlRCJAwUJCwXU2YvFAsjEAcvDwZaFFJNRx1XYQ87JTdaRmhSW1x4WQcyDg1wRhcZEgZfYR8gIyZaHyYGf0xtWVM2BAAxWFIJEgZQNQI9OGNHWiUDAQRjFBIiQ1N+BEZBRxBYMh9yeWMJCi0HEUVHc1N6S0M8WxEMC1RDLgQmdn5aHS0WJwMiDVtzYUNwFFIEAVRfLh9yJCwVDmgWHQkjWQE/HxYiWlILBhhCJEs3OCdwcGhCVUwhFhA7B0MzUiQMCwFUYVZyHy0JDikMFgljFxYtQ0ETcgAMChFnIAcnM2FTcGhCVUwuHyU7BxY1GiQMCwFUYVZyFQUIGyUHWwIoDlspDgQWRh0ATn4RYUtyNSUsGyQXEEIdGAE/BRdwCVIfCBtFS2FydmNaFicBFABtDQQ/Dg1wCVI5EBFULzg3JDUTGS1YNh4oGAc/Q2lwFFJNR1QRYQg0ACIWDy1Of0xtWVN6S0NwYAUIAhp4Lw09eC0fDWAGAB4sDRo1BU9wcRwYClp0IBg7OCQpDjEOEEIBEB0/ChF8FDcDEhkfBAohPy0dPiEQEA85EBw0RSo+ewcZTlg7YUtydmNaWmgZIw0hDBZ6VkMTcgAMChEfLw4lfjAfHRwNXBFHWVN6S0paPlJNR1RdLggzOmMcEyYLBgQoHVNnSwUxWAEIbVQRYUs+OSAbFmgBFAIuHB82DgdwCVILBhhCJGFydmNaDj8HEAJjOhw3Gw81QBcJXTdeLwU3NTdSHD0MFhgkFh1yQmlwFFJNR1QRYQ07OCoJEi0GVVFtDQEvDmlwFFJNAhpVaGFYdmNaWmVPVScoHAN6Hws1FDo/N1RdLgg5MydaDidCAQQoWQctDgY+URZNERVdNA5yMzUfCDFCEx4sFBZQS0NwFB4CBBVdYQg9OC1aR2gwAAIeHAEsAgA1GiAICRBUMzgmMzMKHyxYNgMjFxY5H0s2QRwOEx1eL0N7XGNaWmhCVUxtFRw5Cg9wRlJQRxNUNTk9OTdSU0JCVUxtWVN6Swo2FABNExxUL2FydmNaWmhCVUxtWVMoRSAWRhMAAlQMYQg0ACIWDy1MIw0hDBZQS0NwFFJNR1RULw9YdmNaWi0MEUVHc1N6S0MkQxcICU5hLQorfmpwcGhCVUw6ERo2DkM+WwZNAR1fKBg6MydaHidoVUxtWVN6S0M5UlIJBhpWJBkRPiYZEWgDGwhtHRI0DAYidxoIBB8ZaEsmPiYUcGhCVUxtWVN6S0NwFBEMCRdULQc3MmNHWjwQAAlHWVN6S0NwFFJNR1QRNRw3My1AOSkMFgkhUVpQS0NwFFJNR1QRYUtyNDEfGyNoVUxtWVN6S0M1WhZnR1QRYUtydmMOGzsJWxssEAdyQmlwFFJNAhpVS2FydmNaGScMG1YJEAA5BA0+UREZT107YUtydiAcLCkOAAl3PRYpHxE/TVpEbVQRYUsgMzcPCCZCGwM5WRA7BQA1WB4IA35ULw9YXG5XWgUDHAJtCQY4BwozFAYaAhFfYR4hMydaGDFCFAAhWQAuCgQ1GSY9RxVfJUsiOiIDHzpPITxtGwYuHww+R1xnCxtSIAdyMDYUGTwLGgJtDQQ/Dg0EW1oZBgZWJB8COTBWWjsSEAkpVVM1BSc/WhdEbVQRYUs+OSAbFmgQGgM5WU56DAYkZh0CE1wYS0tydmMTHGgMGhhtCxw1H0MkXBcDRx1XYQQ8EiwUH2gWHQkjWRw0Lww+UVpERxFfJUsgMzcPCCZCEAIpc1N6S0MjRBcIA1QMYRgiMyYeWicQVVl9SXlQS0NwFAYMFB8fMhszIS1SHD0MFhgkFh1yQmlwFFJNR1QRYUZ/dnJUWgMLGQBtPx8jSxA/FDACAw1nJAc9NSoOA2cgGgg0PgooBEMzVRxKE1RDJBg7JTdaFT0QVQEiDxY3Dg0kPlJNR1QRYUtyOiwZGyRCAg0+Px8jAg03FE9NJBJWby0+L0laWmhCVUxtWRo8SyA2U1wrCw0RNQM3OGMpDicSMwA0UVp6Dg00PnhNR1QRYUtydm5XWnpMVSIiGh8zG1lwRBoMFBERNQMgOTYdEmgVFAAhClw1CRAkVREBAgc7YUtydmNaWmgHGw0vFRYUBAA8XQJFTn47YUtydmNaWmhPWEx+V1MYHgo8UFIaBg1BLgI8IjBaDiADAUwlDBR6Hws1FBkIHhdQMUshIzEcGysHf0xtWVN6S0NwWB0OBhgRMh8zJDcqFTtCSEwqHAcIBAwkHFtNBhpVYQw3IhEVFTxKXEIdFgAzHwo/WlICFVRDLgQmeBMVCSEWHAMjc1N6S0NwFFJNCxtSIAdyISIDCicLGxg+WU56CRY5WBYqFRtELw8FNzoKFSEMAR9lCgc7GRcAWwFBRwBQMww3IhMVCWFof0xtWVN6S0NwGV9NU1oRDAQkM2MJHy8PEAI5VBEjRhA1Ux8ICQARNwIzdhEfFCwHBz85HAMqDgdwHAIFHgdYIhh/JjEVFS5Lf0xtWVN6S0NwUh0fRx0RfEtgemNZDSkbBQMkFwcpSwc/PlJNR1QRYUtydmNaWiQNFg0hWQF6VkM3UQY/CBtFaUJYdmNaWmhCVUxtWVN6AgVwWh0ZRwYRNQM3OGMYCC0DHkwoFxdQS0NwFFJNR1QRYUtyOywMHxsHEgEoFwdyGU0AWwEEEx1eL0dyISIDCicLGxg+IhoHR0MjRBcIA107YUtydmNaWmgHGwhHc1N6S0NwFFJNSlkRdEVyFS8fGyYXBWZtWVN6S0NwFBYEFBVTLQ4cOSAWEzhKXGZtWVN6S0NwFF9ARyZUMh89JCZaHCQbVQUrWRouSxQxR1IMBABYNw5yNCYcFToHVRglHFMuHAY1WnhNR1QRYUtydiocWj8DBiohABo0DEMkXBcDbVQRYUtydmNaWmhCVS8rHl0cBxpwCVIZFQFUS0tydmNaWmhCVUxtWSAuChEkch4UT107YUtydmNaWmgHGwhHc1N6S0NwFFJNDhIRLgUWOS0fWjwKEAJtFh0eBA01HFtNAhpVS0tydmMfFCxLfwkjHXlQRk5w1ubhheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffAPl9AR5alw0tyFxYuNWg1PCJtD0V0W0OytOZNNxVFKQ07OCcTFC9CAwUsWUVjSw0xQhsKBgBYLgVyISIDCicLGxg+WVN6S0OyoPBnSlkRo//QdmM9CCcXGwhgHxw2BwwnXRwKRwBGJA48doHNWhgHB0E+DRI9DkMkVQAKAgARg9xyASoUWisNAAI5WR8zBgokFFKP8/Y7bEZytNfumNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//StNf6mNzil/jNm+faiffQ1ubtheCxo//KXElXV2gxEA0/Ght6HAwiXwEdBhdUYQ09JGMbWh8LGy4hFhAxSw01VQBNBlRWKB03OGMKFTsLAQUiF3k2BAAxWFILEhpSNQI9OGMcEyYGIgUjOx81CAgeURMfTwRe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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-wPskiR2F4Bgg
return Vm.run(__src, { name = 'Keyboard escape/keyboard escape', checksum = 1715464684, interval = 2, watermark = 'Y2k-wPskiR2F4Bgg', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
